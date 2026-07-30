/-
Elaboration-time tests for the LaTeX renderers (#16, DESIGN.md §LaTeX-first
display).

Every claim is an EXACT string: the payload is read by MathJax, where a
missing brace or a stray Unicode character is the whole defect. The
`none` guards are the other half of the contract — a value with no natural
LaTeX form must emit no `text/latex` at all, never an approximation.
-/
import CasDsl.Value

namespace CasDslTests

open CasDsl

/-! ## Domains -/

#guard Domain.latex .nat == "\\mathbb{N}"
#guard Domain.latex .int == "\\mathbb{Z}"
#guard Domain.latex .rat == "\\mathbb{Q}"
#guard Domain.latex .real == "\\mathbb{R}"
-- ℤ/5 as the full quotient: `\mathbb{Z}/5` alone reads as a quotient by an
-- element
#guard Domain.latex (.mod 5) == "\\mathbb{Z}/5\\mathbb{Z}"
#guard Domain.latex (.poly .rat) == "\\mathbb{Q}[x]"
#guard Domain.latex (.matrix 2 .rat) == "\\mathrm{Mat}_{2}(\\mathbb{Q})"
#guard Domain.latex (.funcs .real .real) == "\\mathbb{R} \\to \\mathbb{R}"
-- the arrow is a command, not the `→` the plain rendering uses: MathJax does
-- not typeset raw Unicode
#guard Domain.render (.funcs .real .real) == "ℝ → ℝ"

/-! ## Scalars -/

#guard Value.latex? (.int (-3)) == some "-3"
#guard Value.latex? (.rat (mkRat 3 2)) == some "3/2"
-- an integral rational is an integer, not `4/1`
#guard Value.latex? (.rat (mkRat 4 1)) == some "4"
#guard Value.latex? (.mod 5 3) == some "3"

/-! ### Exact algebraic numbers

`\sqrt{}` and `i` are math mode's own spellings, so a surd always HAS a form —
the `√` of the plain rendering is exactly what MathJax would not typeset. A
rational coefficient is parenthesized as in a polynomial, and the imaginary
unit is written `i` rather than `\sqrt{-1}`. -/

#guard Domain.latex .complex == "\\mathbb{C}"
#guard Value.latex? (.alg 0 1 2) == some "\\sqrt{2}"
#guard Value.latex? (.alg 0 2 2) == some "2\\sqrt{2}"
#guard Value.latex? (.alg 0 1 (-1)) == some "i"
#guard Value.latex? (.alg 0 (-1) (-1)) == some "-i"
#guard Value.latex? (.alg 2 2 (-1)) == some "2 + 2i"
#guard Value.latex? (.alg 2 (-2) (-1)) == some "2 - 2i"
#guard Value.latex? (.alg 0 2 (-3)) == some "2i\\sqrt{3}"
-- SPEC.md's ℂ[x] factorization writes the roots (−1 ± √5)/2, which this
-- presentation spells with the inline solidus its rationals already use
#guard Value.latex? (.alg (mkRat (-1) 2) (mkRat 1 2) 5)
  == some "-1/2 + (1/2)\\sqrt{5}"
-- (that every payload is ASCII math mode — no `√`, no `ℂ` — is asserted over
-- the real bundles in tests/test_e2e.py, where `str.isascii` lives)

-- the plain renderings, in the same order
#guard Value.render (.alg 0 1 2) == "√2"
#guard Value.render (.alg 0 2 2) == "2√2"
#guard Value.render (.alg 2 2 (-1)) == "2 + 2i"
#guard Value.render (.alg 2 (-2) (-1)) == "2 - 2i"
#guard Value.render (.alg 0 2 (-3)) == "2i√3"
#guard Value.render (.alg (mkRat (-1) 2) (mkRat 1 2) 5) == "-1/2 + (1/2)√5"

-- a coefficient that is not a plain integer is parenthesized, so a surd
-- coefficient reads as a product rather than as a sum that swallowed the
-- indeterminate
#guard Value.render (.poly .complex #[.int 1, .alg 2 2 (-1)]) == "(2 + 2i)x + 1"
#guard Value.latex? (.poly .complex #[.int 1, .alg 2 2 (-1)])
  == some "(2 + 2i)x + 1"
#guard Value.render (.poly .real #[.int 0, .alg 0 2 2]) == "(2√2)x"

/-! ## Polynomials

The issue's showcase shape, plus the cases that break a naive renderer: a
negative coefficient, a zero coefficient (dropped, not printed as `+ 0x^2`),
a rational coefficient, and a MULTI-DIGIT exponent, which is exactly why the
braces are unconditional. -/

-- x³ - 2x + 1  (issue #16, showcase 3)
#guard Value.latex? (.poly .int #[.int 1, .int (-2), .int 0, .int 1])
  == some "x^{3} - 2x + 1"
#guard Value.latex? (.poly .int #[]) == some "0"
#guard Value.latex? (.poly .int #[.int 7]) == some "7"
#guard Value.latex? (.poly .int #[.int 0, .int (-1)]) == some "-x"
#guard Value.latex? (.poly .rat #[.int 0, .rat (mkRat 1 2)]) == some "(1/2)x"
-- x^{12}: unbraced, `x^12` typesets as x¹·2
#guard Value.latex? (.poly .int ((List.replicate 12 (Value.int 0)).toArray.push (.int 1)))
  == some "x^{12}"

/-! ## Matrices -/

-- M⁻¹ for M = [1, 2; 3, 4] over ℚ  (issue #16, showcase 1)
#guard Value.latex?
    (.mat 2 .rat #[#[.rat (mkRat (-2) 1), .rat (mkRat 1 1)],
                   #[.rat (mkRat 3 2), .rat (mkRat (-1) 2)]])
  == some "\\begin{pmatrix} -2 & 1 \\\\ 3/2 & -1/2 \\end{pmatrix}"

/-! ## Factorizations -/

-- 360 = 2³ · 3² · 5  (issue #16, showcase 2)
#guard Value.latex? (.factorization (.int 1) #[(.int 2, 3), (.int 3, 2), (.int 5, 1)] .int)
  == some "2^{3} \\cdot 3^{2} \\cdot 5"
-- SPEC.md §Polynomials: the factors of x³ - 2x + 1, each one parenthesized
#guard Value.latex?
    (.factorization (.int 1)
      #[(.poly .int #[.int (-1), .int 1], 1),
        (.poly .int #[.int (-1), .int 1, .int 1], 1)] (.poly .int))
  == some "(x - 1) \\cdot (x^{2} + x - 1)"
-- the factorization of a CONSTANT: no factors, unit 1, in both spellings of
-- the unit. An empty `core` would ship `$$$$`, which is not a display
#guard Value.latex? (.factorization (.rat (mkRat 1 1)) #[] (.poly .rat)) == some "1"
#guard Value.render (.factorization (.rat (mkRat 1 1)) #[] (.poly .rat)) == "1"
#guard Value.latex? (.factorization (.int 1) #[] .int) == some "1"
-- a REPEATED polynomial factor keeps its multiplicity: the exponent is the
-- part a `do`-block `return` in the factor loop silently drops
#guard Value.latex?
    (.factorization (.int 1) #[(.poly .int #[.int (-1), .int 1], 2)] (.poly .int))
  == some "(x - 1)^{2}"
-- a unit that is not 1 stays in front
#guard Value.latex? (.factorization (.int (-1)) #[(.int 2, 1)] .int)
  == some "-1 \\cdot 2"
-- …and a RATIONAL unit is a scalar like any other, so an integral one is an
-- integer: `2 * (x - 1) * (x + 1)` is what ℚ[x] factorization returns, and
-- `2/1` there would contradict the scalar convention pinned above
#guard Value.latex?
    (.factorization (.rat (mkRat 2 1))
      #[(.poly .rat #[.int (-1), .int 1], 1), (.poly .rat #[.int 1, .int 1], 1)]
      (.poly .rat))
  == some "2 \\cdot (x - 1) \\cdot (x + 1)"

/-! ## Sets -/

#guard SetPresentation.latex? (.finite .int #[.int 1, .int 2, .int 3])
  == some "\\{1, 2, 3\\}"
#guard SetPresentation.latex? (.finite .int #[]) == some "\\{\\}"
#guard SetPresentation.latex? (.arithProg .nat (.int 0) (.int 2) none)
  == some "\\{0, 2, \\ldots\\}"
#guard SetPresentation.latex? (.arithProg .int (.int 0) (.int 2) (some (.int 10)))
  == some "\\{0, 2, \\ldots, 10\\}"
#guard SetPresentation.latex? (.domainSet .int) == some "\\mathbb{Z}"
#guard SetPresentation.latex?
    (.product (.finite .int #[.int 1]) (.domainSet .nat))
  == some "\\{1\\} \\times \\mathbb{N}"
#guard SetPresentation.latex? (.powerset (.finite .int #[.int 1, .int 2]))
  == some "\\mathcal{P}(\\{1, 2\\})"
-- `ℂ - ℚ`: a minus between two SETS is `\setminus` in math mode, and the
-- plain rendering keeps SPEC.md's own spelling
#guard SetPresentation.latex? (.domainDiff .complex .rat)
  == some "\\mathbb{C} \\setminus \\mathbb{Q}"
#guard SetPresentation.render (.domainDiff .complex .rat) == "ℂ - ℚ"

/-! ## Cardinals, functions, ideals -/

#guard Value.latex? (.cardinal (.finite 9)) == some "9"
#guard Value.latex? (.cardinal .countablyInfinite) == some "\\aleph_0"
-- SPEC.md §Functions: `h := t ↦ t² + 1`, in the mathematician's own binder
#guard Value.latex? (.func .real .real `t (.poly .real #[.int 1, .int 0, .int 1]))
  == some "t \\mapsto t^{2} + 1"
#guard Value.latex? (.idealV #[.int 4] .int) == some "(4)"

/-! ## No natural form — the documented fallback

These must be `none`, not a best effort: the cell then emits `text/plain`
alone. -/

#guard Value.latex? (.bool true) == none
#guard Value.latex? (.bool false) == none
-- a binder the mathematician spelled with a non-ASCII letter: `θ` is not a
-- LaTeX command, and raw Unicode in math mode is a hard error downstream, so
-- the whole function falls back to plain text rather than shipping it
#guard Value.latex? (.func .real .real `θ (.poly .real #[.int 1, .int 1])) == none
-- …and an ASCII binder that is not LaTeX-safe either: `x_1_2` is a double
-- subscript (a pdflatex error) and `x_ab` typesets as x_a b, silently wrong.
-- Subscript typography is NOT invented here; the fallback is plain text
#guard Value.latex? (.func .real .real `x_1_2 (.poly .real #[.int 1, .int 1])) == none
#guard Value.latex? (.func .real .real `x_ab (.poly .real #[.int 1, .int 1])) == none
-- a coefficient with no LaTeX form takes the whole polynomial with it,
-- exactly as an element does for a set — otherwise the plain spelling of a
-- value this renderer cannot typeset would go RAW into a math-mode payload
#guard Value.latex? (.poly .int #[.bool true]) == none
#guard Value.render (.poly .int #[.bool true]) == "true"
#guard Value.latex? (.func .real .real `t (.poly .real #[.int 1, .bool true])) == none
#guard Value.latex? (.factorization (.int 1) #[(.poly .int #[.bool true], 1)] .int) == none
-- the module fixture: `\mathbb{Z}/4\mathbb{Z}` typeset alone is the RING, and
-- equality here is category-bound
#guard Obj.latex? (.cyclicModule 4) == none
-- …while its plain rendering says what it is
#guard Obj.render (.cyclicModule 4) == "ℤ/4 as ℤ-module"
-- `none` propagates out of a container: a set of truth values has no form
#guard SetPresentation.latex? (.finite .int #[.bool true]) == none

/-! ## Objects -/

#guard Obj.latex? (.elem .int (.int 7)) == some "7"
#guard Obj.latex? (.domainObj (.poly .int)) == some "\\mathbb{Z}[x]"
#guard Obj.latex? (.setObj (.finite .int #[.int 1])) == some "\\{1\\}"

end CasDslTests
