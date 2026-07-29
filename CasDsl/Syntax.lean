/-
The surface syntax: a `casTerm` category plus command elaborators. Nothing
outside Lean interprets any of this — notebook cells reach the worker
verbatim.

Parser notes (hard-won, load-bearing):
- The `let` COMMAND is declared LAST in this file. Declared earlier it
  shadows `let x := e` inside every subsequent `do` block in this module at
  parse time (the nbdsl lore); every elaborator body below the command
  block is therefore a single call into a helper defined above it.
- Commands end at newline; a `.` terminator would conflict with field
  projection.
- `n.factor` lexes as ONE hierarchical identifier — Lean's `ident` parser
  eats the dot. So `e.m(args)` is parsed as a plain call on a dotted name
  and split into receiver/method here, which is also why the receiver of a
  method call is a name rather than an arbitrary expression.
- `noWs` before `(` and `[` is what keeps a bare-expression cell from
  swallowing the next line: without it, `X.cardinality()` followed by
  `[1, 2; 3, 4]` parses as one indexing expression.
- Implicit multiplication is `numeral noWs ident` only (`2x`), for the same
  reason: `assert 2 + 3 = 5` followed by a line starting with an identifier
  must not become a product.
- `...` is declared as a token; `..` already is one, and the tokenizer's
  longest match keeps them apart.
-/
import CasDsl.Eval
import CasDsl.Codec
import Worker.Output

namespace CasDsl

open Lean Elab Command
open Worker (emitOutput)

/-! ## The `casTerm` category

Precedence ladder (Lean's own conventions, restricted to what a CAS surface
needs): `+ -` at 65, `* /` at 70, unary `-` at 75, `^` at 80 (right
associative), atoms and postfix chains at max. -/

declare_syntax_cat casTerm
declare_syntax_cat casSetItem
declare_syntax_cat casRel

syntax:max (name := casNatDom) "ℕ" : casTerm
syntax:max (name := casIntDom) "ℤ" : casTerm
syntax:max (name := casRatDom) "ℚ" : casTerm
syntax:max (name := casImplMul) num noWs ident : casTerm
syntax:max (name := casNum) num : casTerm
syntax:max (name := casIdent) ident : casTerm
syntax:max (name := casParen) "(" casTerm ")" : casTerm
syntax:max (name := casSet) "{" casSetItem,* "}" : casTerm

syntax casRow := casTerm,+
syntax:max (name := casMat) "[" sepBy1(casRow, "; ") "]" : casTerm

syntax (name := casEllipsis) "..." : casSetItem
syntax (name := casSetElem) casTerm : casSetItem

syntax:max (name := casIndex) casTerm:max noWs "[" casTerm "]" : casTerm
syntax:max (name := casApply) casTerm:max noWs "(" casTerm,* ")" : casTerm

syntax:80 (name := casPow) casTerm:81 " ^ " casTerm:80 : casTerm
syntax:75 (name := casNeg) "-" casTerm:75 : casTerm
syntax:70 (name := casMul) casTerm:70 " * " casTerm:71 : casTerm
syntax:70 (name := casDiv) casTerm:70 " / " casTerm:71 : casTerm
syntax:65 (name := casAdd) casTerm:65 " + " casTerm:66 : casTerm
syntax:65 (name := casSub) casTerm:65 " - " casTerm:66 : casTerm
syntax:20 (name := casMap) "map " casTerm:21 " to " casTerm:21 : casTerm

syntax (name := casRelEq) "=" : casRel
syntax (name := casRelNe) "≠" : casRel
syntax (name := casRelMem) "∈" : casRel
syntax (name := casRelNotMem) "∉" : casRel

/-! ## Syntax → `CasExpr` -/

private def subscriptDigit? (c : Char) : Option Nat :=
  if c.toNat ≥ '₀'.toNat && c.toNat ≤ '₉'.toNat then some (c.toNat - '₀'.toNat)
  else none

/-- `Mat₂` → `2`. Any size expressible in subscript digits is accepted; the
renderer in `Value.lean` produces exactly this spelling. -/
def matSize? (n : Name) : Option Nat :=
  match n with
  | .str .anonymous s =>
      if !s.startsWith "Mat" then none
      else
        let ds := s.toList.drop 3
        if ds.isEmpty then none
        else ds.foldlM (init := 0) fun acc c => (subscriptDigit? c).map (10 * acc + ·)
  | _ => none

/-- Split a dotted name into receiver and final component. -/
private def splitMethod? : Name → Option (Name × Name)
  | .str p s => if p == .anonymous then none else some (p, Name.mkSimple s)
  | _ => none

private def natLit (stx : Syntax) : Except String Nat :=
  match stx.isNatLit? with
  | some n => .ok n
  | none => .error s!"expected a numeral, got {stx}"

partial def toExpr (stx : Syntax) : Except String CasExpr := do
  match stx.getKind with
  | ``casNatDom => return .dom .nat
  | ``casIntDom => return .dom .int
  | ``casRatDom => return .dom .rat
  | ``casNum => return .num (Int.ofNat (← natLit stx[0]))
  | ``casImplMul =>
      return .bin .mul (.num (Int.ofNat (← natLit stx[0]))) (.ref stx[1].getId)
  | ``casIdent => return .ref stx[0].getId
  | ``casParen => toExpr stx[1]
  | ``casNeg => return .neg (← toExpr stx[1])
  | ``casAdd => return .bin .add (← toExpr stx[0]) (← toExpr stx[2])
  | ``casSub => return .bin .sub (← toExpr stx[0]) (← toExpr stx[2])
  | ``casMul => return .bin .mul (← toExpr stx[0]) (← toExpr stx[2])
  | ``casDiv => return .bin .div (← toExpr stx[0]) (← toExpr stx[2])
  | ``casPow => return .bin .pow (← toExpr stx[0]) (← toExpr stx[2])
  | ``casMap => return .mapTo (← toExpr stx[1]) (← toExpr stx[3])
  | ``casIndex => return .index (← toExpr stx[0]) (← toExpr stx[2])
  | ``casApply => do
      let args ← stx[2].getSepArgs.mapM toExpr
      match ← toExpr stx[0] with
      | .ref nm =>
          match matSize? nm with
          | some k =>
              if h : args.size = 1 then return .matDom k (args[0]'(by simp [h]))
              else .error s!"Mat{k}(…) takes one entry domain, got {args.size}"
          | none =>
              match splitMethod? nm with
              | some (recv, m) => return .method (.ref recv) m args
              | none => return .app (.ref nm) args
      | f => return .app f args
  | ``casSet => do
      let items := stx[1].getSepArgs
      let ellipses := (items.toList.zipIdx).filterMap fun (it, i) =>
        if it.getKind == ``casEllipsis then some i else none
      let elems ← items.filterMap (fun it =>
        if it.getKind == ``casEllipsis then none else some it[0]) |>.mapM toExpr
      match ellipses with
      | [] => return .finSet elems
      | [i] =>
          if i + 1 == items.size then return .progSet elems none
          else if i + 2 == items.size then
            let some last := elems.back?
              | .error "a bounded progression needs a leading element"
            return .progSet elems.pop (some last)
          else .error "`...` may only be the last or the second-to-last element \
of a set literal"
      | _ => .error "a set literal contains at most one `...`"
  | ``casMat => do
      let rows := stx[1].getSepArgs
      let cells := rows.map fun r =>
        if r.getKind == ``casRow then r[0].getSepArgs else r.getSepArgs
      let some cols := (cells[0]? : Option (Array Syntax)).map (·.size)
        | .error "a matrix literal needs at least one row"
      if cells.any (·.size != cols) then
        .error "every row of a matrix literal must have the same length"
      return .matLit cells.size cols (← cells.flatten.mapM toExpr)
  | k => .error s!"unsupported cas syntax node '{k}'"

/-! ## Rendering results -/

private def valueJson (d : Denote) : Json :=
  match d.value? with
  | some v => Codec.valueToJson v
  | none => Json.null

private def denoteJson (d : Denote) : Json :=
  Json.mkObj
    [("render", .str d.render),
     ("presentation", .str d.presentation),
     ("value", valueJson d)]

/-! ## Elaborator helpers

Defined ABOVE the command block so their `do`/`let` bodies parse before the
`let` command production exists. -/

private def parseCas (stx : Syntax) : CommandElabM CasExpr := do
  match toExpr stx with
  | .ok e => return e
  | .error m => throwError m

private def casCtx (ambient? : Option Domain := none) : CommandElabM EvalCtx := do
  return { env := ← getEnv, ambient? }

private def runCas (x : EvalM α) : CommandElabM α := do
  match ← x.run with
  | .ok a => return a
  | .error e => throwError e.render

/-- The source text of a syntax node, for echoing an assertion back at the
mathematician in the spelling they wrote. -/
private def src (stx : Syntax) : String :=
  (stx.reprint.getD (toString stx)).trimAscii.toString

/-- The optional `in <casTerm>` tail of a command. -/
private def optTail? (stx : Syntax) : Option Syntax :=
  if stx.isNone then none else some stx[1]

private def ambientOf (tail? : Option Syntax) : CommandElabM (Option Domain) := do
  match tail? with
  | none => return none
  | some t =>
      match ← runCas (eval (← casCtx) (← parseCas t)) with
      | .obj (.domainObj d) => return some d
      | other => throwError s!"`in {other.render}` is not a domain"

private def bindObj (n : Name) (o : Obj) : CommandElabM Unit := do
  modifyEnv fun env => addBinding env (n, o)
  logInfo s!"{n} := {o.presentation}"

def elabCasLet (idStx valStx : Syntax) (asc? : Option Syntax) : CommandElabM Unit := do
  let e ← parseCas valStx
  let a? ← asc?.mapM parseCas
  bindObj idStx.getId (← runCas (evalBinding (← casCtx) e a?))

def elabCasLetPoly (idStx xStx valStx ascStx : Syntax) : CommandElabM Unit := do
  let e ← parseCas valStx
  let a ← parseCas ascStx
  bindObj idStx.getId (← runCas (evalPolyBinding (← casCtx) xStx.getId e a))

def elabCasAssert (lhs relStx rhs : Syntax) (tail? : Option Syntax)
    : CommandElabM Unit := do
  let rel : AssertRel ← match relStx.getKind with
    | ``casRelEq => pure .eq
    | ``casRelNe => pure .ne
    | ``casRelMem => pure .mem
    | ``casRelNotMem => pure .notMem
    | k => throwError s!"unsupported assertion relation '{k}'"
  let l ← parseCas lhs
  let r ← parseCas rhs
  let ctx ← casCtx (← ambientOf tail?)
  let stated := s!"{src lhs} {rel.render} {src rhs}"
    ++ (tail?.elim "" fun t => s!" in {src t}")
  match ← runCas (evalAssert ctx rel l r) with
  | some true => logInfo s!"✓ {stated}"
  | some false => throwError s!"assertion is false: {stated}"
  | none => throwError s!"the assertion outcome is unknown: the two sides of \
{stated} are not comparable"

/-- A bare expression cell: display the value as text and as a structured
MIME bundle. -/
def elabCasShow (stx : Syntax) : CommandElabM Unit := do
  let d ← runCas (eval (← casCtx) (← parseCas stx))
  logInfo d.render
  emitOutput {
    data :=
      [("text/plain", .str d.render),
       ("application/vnd.casdsl.value+json", denoteJson d)]
  }

/-! ## Commands

Declared last (see the header note). Every elaborator below is one call. -/

/-- `let x := e [in T]` binds `x` to the value of `e`. The ascription `T` is
a checked membership judgment, not an annotation: a domain must admit the
preferred embedding, and a registered category must actually contain the
object. Set literals need no ascription. -/
syntax (name := casLet) "let " ident " := " casTerm (" in " casTerm)? : command

/-- `let p(x) := e in D[x]` binds a univariate polynomial: the ascription
supplies the coefficient domain, and `x` denotes the indeterminate inside
`e`. -/
syntax (name := casLetPoly)
  "let " ident noWs "(" ident ")" " := " casTerm " in " casTerm : command

/-- `assert l (= | ≠ | ∈ | ∉) r [in D]` — a TRUSTED COMPUTATIONAL assertion
in the ordinary CAS sense. The predicate is computed and believed; no Lean
proposition is created, no theorem is generated, and no certificate is
required. The outcome is fourfold — `true | false | unknown | error` — and
only `true` lets the cell commit, so a failed assertion rolls the cell's
registrations back with the worker's cell atomicity. `in D` sets the ambient
domain the literals and arithmetic are read in. -/
syntax (name := casAssert)
  "assert " casTerm casRel casTerm (" in " casTerm)? : command

/-- A bare expression cell displays its value. Low priority, so every
genuine Lean command in a cell still parses as Lean. -/
syntax (name := casShow) (priority := low) casTerm : command

@[command_elab casLet]
def elabLetCmd : CommandElab := fun stx =>
  elabCasLet stx[1] stx[3] (optTail? stx[4])

@[command_elab casLetPoly]
def elabLetPolyCmd : CommandElab := fun stx =>
  elabCasLetPoly stx[1] stx[3] stx[6] stx[8]

@[command_elab casAssert]
def elabAssertCmd : CommandElab := fun stx =>
  elabCasAssert stx[1] stx[2] stx[3] (optTail? stx[4])

@[command_elab casShow]
def elabShowCmd : CommandElab := fun stx => elabCasShow stx[0]

end CasDsl
