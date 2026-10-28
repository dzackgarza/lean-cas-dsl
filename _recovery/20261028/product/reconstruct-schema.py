"""Recover external patch candidates only. No Lean, no live source writes.

This script reconstructs retained source transformations. A candidate is exact only
if its final SHA equals f0e2ad4790eda9c57668fc58289cf91c358b2da423f711caf113ec20b3de7b22.
Missing later baseline context must not be called recovered exact source.
Run with --emit to print the candidate patch; otherwise it validates replacements
and prints fragment hashes. It never writes either repository.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import re

ROOT = Path('/workspace/scratch/4e9256f8ceed')
HERE = ROOT / 'recovery-20261028/product'
KERNEL = ROOT / 'lean-cas-dsl-kernel'
CONTRACT = ROOT / 'lean-cas-dsl-leaf-contracts-lift'


def replace_once(text, old, new):
    assert text.count(old) == 1, (text.count(old), old)
    return text.replace(old, new)


def segment(text, start, end, callback):
    a, b = text.index(start), text.index(end)
    return text[:a] + callback(text[a:b]) + text[b:]


def sub_count(pattern, replacement, text, count):
    result, actual = re.subn(pattern, replacement, text)
    assert actual == count, (pattern, actual, count)
    return result


def fragment(path, old, new):
    diff = list(difflib.unified_diff(old.splitlines(), new.splitlines(), n=3))[2:]
    body = '\n'.join('@@' if line.startswith('@@ ') else line for line in diff)
    return '*** Update File: ' + str(path) + '\n' + body + '\n'


def object_presentation():
    path = KERNEL / 'CasCatalogue/ObjectPresentation.lean'
    old = path.read_text()
    if '| "component" =>' not in old:
        old = replace_once(old, '  | "constants" => entry.constants\n',
            '  | "constants" => entry.constants\n  | "component" => entry.components.map (·.projection)\n')
    assert hashlib.sha256(old.encode()).hexdigest() == 'f17f58e6402dbe25bc218da85651f2dded00a33b9c235f296860092d41e550d7'
    additions = (HERE / 'component-interface-recovered.lean').read_text()
    # The original ObjectPresentation fragment was hand-authored with these
    # exact contexts; unlike the other fragments, it did not use difflib.
    before = '''def applyParameters (declaration : Name) (parameters : Array Expr) : TermElabM Expr := do
  elabTermAndSynthesize
    (← `($(mkCIdent declaration) $(← parameters.mapM exprToSyntax)*)) none'''
    field = '''def field (entry : ObjectEntry) (selector : String) (parameters : Array Expr)
    (trace? : Option Trace := none) : TermElabM Expr := do
  let some declaration := fieldDeclaration entry selector
    | throwError "the registered object has no {selector} field"
  let application ← applyParameters declaration parameters
  let value ← instantiateMVars (← fieldValue selector application)'''
    field_new = '''def field (entry : ObjectEntry) (selector : String) (parameters : Array Expr)
    (trace? : Option Trace := none) (original? : Option Expr := none) : TermElabM Expr := do
  let some declaration := fieldDeclaration entry selector
    | throwError "the registered object has no {selector} field"
  let application ← if selector == "component" then
      componentApplication entry parameters original?
    else applyParameters declaration parameters
  let value ← instantiateMVars (← fieldValue selector application)'''
    new = replace_once(old, 'public import CasCatalogue.Semantic\n',
        'public import CasCatalogue.Semantic\npublic import CasCatalogue.DirectConstruction\n')
    new = replace_once(new, before, before + '\n\n' + additions.rstrip())
    new = replace_once(new, field, field_new)
    assert hashlib.sha256(new.encode()).hexdigest() == '0679bed629bb03ed2c91088f5a3388401e44cde6fe326498223f8d200834ef3b'
    body = '*** Update File: ' + str(path) + '\n@@\n public import CasCatalogue.Semantic\n+public import CasCatalogue.DirectConstruction\n@@\n'
    body += '\n'.join(' ' + line for line in before.splitlines()) + '\n+\n'
    body += '\n'.join('+' + line for line in additions.rstrip().splitlines()) + '\n@@\n'
    body += ''' def field (entry : ObjectEntry) (selector : String) (parameters : Array Expr)
-    (trace? : Option Trace := none) : TermElabM Expr := do
+    (trace? : Option Trace := none) (original? : Option Expr := none) : TermElabM Expr := do
   let some declaration := fieldDeclaration entry selector
     | throwError "the registered object has no {selector} field"
-  let application ← applyParameters declaration parameters
+  let application ← if selector == "component" then
+      componentApplication entry parameters original?
+    else applyParameters declaration parameters
   let value ← instantiateMVars (← fieldValue selector application)
'''
    return body


def computational_data():
    path = KERNEL / 'CasCatalogue/ComputationalData.lean'
    old = path.read_text()
    def port(s):
        s = replace_once(s,
            '''(declarationPorts : Name → Expr → Expr → Array Json → InterfaceObjects →
      Option InterfaceScope → TermElabM (Except String Unit))''',
            '''(declarationPorts : Name → Expr → Expr → Array Json → InterfaceObjects →
      Option InterfaceScope → Option Expr → TermElabM (Except String Unit))''')
        s = sub_count(r'(declarationPorts [^\n]*?\(InterfaceScope\.(?:args|arg)\? scope(?: 2)?\))', r'\1 none', s, 7)
        return replace_once(s,
            '''      return ← declarationPorts declaration formalField expectedType parameters objects (InterfaceScope.arg? scope 2) none
    if tag == "powerObjectMap" then''',
            '''      let family? ← ObjectPresentation.fieldFamily? entry field
      return ← declarationPorts declaration formalField expectedType parameters objects
        (InterfaceScope.arg? scope 2) family?
    if tag == "powerObjectMap" then''')
    new = segment(old, 'def validatePortWith\n', 'def validatePublicDataWith\n', port)
    def public(s):
        s = replace_once(s, 'Name → Array Json → TermElabM', 'Name → Array Json → Option Expr → TermElabM')
        s = sub_count(r'\bvalidateDeclaredData ([A-Za-z0-9_.]+) ([A-Za-z0-9_.]+)', r'validateDeclaredData \1 \2 none', s, 17)
        return replace_once(s,
            '''    return ← validateDeclaredData declaration parameters none
  if tag == "presentation" then''',
            '''    let family? ← if tag == "objectField" then
        match state.objects.find? (·.id.raw == id) with
        | some entry => ObjectPresentation.fieldFamily? entry field
        | none => pure none
      else pure none
    return ← validateDeclaredData declaration parameters family?
  if tag == "presentation" then''')
    new = segment(new, 'def validatePublicDataWith\n', 'def validateCallableAtWith\n', public)
    def callable(s):
        s = replace_once(s, 'Option DataEndpointReader →', 'Option DataEndpointReader → Option Expr →')
        s = sub_count(r'(\binterfaceDeclaration objects[\s\S]*?\bdataEndpoints)', r'\1 none', s, 8)
        return replace_once(s,
            '''      return (← interfaceDeclaration objects declaration expected parameters
        (InterfaceScope.arg? scope 2) dataEndpoints none).map fun _ => ()''',
            '''      let family? ← if tag == "objectField" then
          match state.objects.find? (·.id.raw == id) with
          | some entry => ObjectPresentation.fieldFamily? entry field
          | none => pure none
        else pure none
      return (← interfaceDeclaration objects declaration expected parameters
        (InterfaceScope.arg? scope 2) dataEndpoints family?).map fun _ => ()''')
    new = segment(new, 'def validateCallableAtWith\n', 'mutual\n/-- Validate the public declaration', callable)
    new = replace_once(new,
        '''partial def declarationPorts (declaration : Name) (formal expected : Expr)
    (args : Array Json) (objects : InterfaceObjects := #[]) (scope : Option InterfaceScope := none) :
    TermElabM (Except String Unit) := do''',
        '''partial def declarationPorts (declaration : Name) (formal expected : Expr)
    (args : Array Json) (objects : InterfaceObjects := #[]) (scope : Option InterfaceScope := none)
    (family? : Option Expr := none) : TermElabM (Except String Unit) := do''')
    def constants(s):
        return replace_once(s, '  let constant ← mkConstWithFreshMVarLevels declaration',
            '''  let constant ← match family? with
    | some family => pure family
    | none => mkConstWithFreshMVarLevels declaration''')
    new = segment(new, 'partial def declarationPorts ', 'partial def validatePort ', constants)
    new = replace_once(new, 'interfaceDeclaration objects declaration expected args scope',
        'interfaceDeclaration objects declaration expected args scope none family?')
    new = replace_once(new,
        '''    (fun declaration formal expected args objects scope =>
      declarationPorts declaration formal expected args objects scope)''',
        '''    (fun declaration formal expected args objects scope family? =>
      declarationPorts declaration formal expected args objects scope family?)''')
    new = replace_once(new,
        '''partial def validateDeclaredData (declaration : Name) (data : Array Json) :
    TermElabM (Except String Unit) := do''',
        '''partial def validateDeclaredData (declaration : Name) (data : Array Json)
    (family? : Option Expr := none) : TermElabM (Except String Unit) := do''')
    new = segment(new, 'partial def validateDeclaredData ', 'partial def validatePublicData ', constants)
    new = replace_once(new,
        '''  for (type, datum) in types.zip data do
    if (← plainType type) then
      if let .error message ← Codec.decode type datum then return .error message
    else if let .error message ← validatePublicData datum then return .error message''',
        '''  for (type, datum) in types.zip data do
    let .ok payload := valuePayload datum
      | return .error "a declaration parameter has an incomplete transparent value envelope"
    let opaque := (payload.getObjValAs? String "ctor").toOption == some "opaqueData"
    if !opaque && !type.hasMVar && !type.hasLevelMVar && (← plainType type) then
      if let .error message ← Codec.decode type payload then return .error message
    else if let .error message ← validatePublicData datum then return .error message''')
    new = replace_once(new, '(fun declaration data => validateDeclaredData declaration data)',
        '(fun declaration data family? => validateDeclaredData declaration data family?)')
    new = replace_once(new,
        '(dataEndpoints : Option DataEndpointReader := none) :\n',
        '(dataEndpoints : Option DataEndpointReader := none) (family? : Option Expr := none) :\n')
    new = segment(new, 'partial def interfaceDeclaration ', 'partial def interfaceArgument ', constants)
    new = replace_once(new,
        '  return .ok (← instantiateMVars (mkAppN constant fields))',
        '  return .ok (← instantiateMVars (mkAppN constant fields).headBeta)')
    new = replace_once(new,
        '''    (fun objects declaration expected data scope endpoints =>
      interfaceDeclaration objects declaration expected data scope endpoints)''',
        '''    (fun objects declaration expected data scope endpoints family? =>
      interfaceDeclaration objects declaration expected data scope endpoints family?)''')
    def argument(s):
        s = replace_once(s,
            '  if let some _ := Language.homEnds? expected then',
            '''  if (data.getObjValAs? String "ctor").toOption == some "valueData" then
    let .ok ("valueData", #[actual]) := envelope data
      | return .error "a declaration parameter has an incomplete transparent value envelope"
    return ← interfaceArgument objects expected actual
      (InterfaceScope.body? scope #[.field "args", .index 0])
  if let some _ := Language.homEnds? expected then''')
        return replace_once(s,
            '''  if ← plainType expected then return ← Codec.decode expected data
  let placeholder ← mkFreshExprMVar expected''',
            '''  if (data.getObjValAs? String "ctor").toOption != some "opaqueData" && (← plainType expected) then
    return ← Codec.decode expected data
  let placeholder ← mkFreshExprMVar expected''')
    # The mutual block contains interfaceArgument after interfaceDeclaration.
    begin = new.index('partial def interfaceArgument ')
    new = new[:begin] + argument(new[begin:])
    return fragment(path, old, new)


def realize():
    path = KERNEL / 'CasCatalogue/Realize.lean'
    old = path.read_text()
    new = replace_once(old,
        '(accepted? : Option Expr := none) (completeParameters : Bool := false) :',
        '(accepted? : Option Expr := none) (completeParameters : Bool := false)\n    (family? : Option Expr := none) :')
    a, b = new.index('def decodeFamily '), new.index('def decodeDeclaration ')
    new = new[:a] + replace_once(new[a:b], '  let c ← mkConstWithFreshMVarLevels declaration',
        '''  let c ← match family? with
    | some family => pure family
    | none => mkConstWithFreshMVarLevels declaration''') + new[b:]
    new = replace_once(new, 'return .ok (← instantiateMVars (mkAppN c mvars), decoded)',
        'return .ok (← instantiateMVars (mkAppN c mvars).headBeta, decoded)')
    new = replace_once(new,
        '''def decodeDeclaration (declaration : Name) (expected : Expr) (args : Array Json)
    (decodeArg : Expr → Json → TermElabM (Except String (Expr × Option Form))) :
    TermElabM (Except String (Expr × Array (Expr × Option Form))) :=
  decodeFamily declaration expected args decodeArg none true''',
        '''def decodeDeclaration (declaration : Name) (expected : Expr) (args : Array Json)
    (decodeArg : Expr → Json → TermElabM (Except String (Expr × Option Form)))
    (family? : Option Expr := none) :
    TermElabM (Except String (Expr × Array (Expr × Option Form))) :=
  decodeFamily declaration expected args decodeArg none true family?''')
    a = new.index('partial def decodeValue ')
    insert = new.index(' := do\n', a) + len(' := do\n')
    new = new[:insert] + '''  if (j.getObjValAs? String "ctor").toOption == some "valueData" then
    let .ok (.inline actual) := Backend.ComputationalValue.decode j
      | return .error "the declared parameter has an incomplete transparent value envelope"
    return ← decodeValue trace category type actual
''' + new[insert:]
    new = replace_once(new,
        '''    let expected ← inferType (← instantiateFresh declaration)
    let .ok (application, _) ← decodeDeclaration declaration expected params (decodeValue trace category)
      | return .error "the object field parameters do not decode at their declared types"''',
        '''    let expected ← inferType (← instantiateFresh declaration)
    let family? ← ObjectPresentation.fieldFamily? entry field
    let .ok (application, _) ← decodeDeclaration declaration expected params
        (decodeValue trace category) family?
      | return .error "the object field parameters do not decode at their declared types"''')
    new = replace_once(new, 'let actual ← ObjectPresentation.field entry field params',
        'let actual ← ObjectPresentation.field entry field params (original? := some e)')
    return fragment(path, old, new)


DOC_CHANGES = {
    'CasContract/Port.lean': [
        ('''  The field `component` selects `ObjectEntry.components.projection`, with every explicit
  object parameter followed by its selected index in `Fin (components.arity parameters)`.''',
         '''  The field `component` selects `ObjectEntry.components.projection`, with the object's
  explicit data parameters (proof parameters omitted) followed by a mandatory selected index
  in `Fin (components.arity parameters)`. This order follows the object declaration even when
  the projection uses different implicit binders; the index is always present in the wire.'''),
        ('''The component field selects `ObjectEntry.components.projection`; its final explicit
parameter is the index in the declared finite coordinate type. Like other parameters,''',
         '''The component field selects `ObjectEntry.components.projection` at the object's explicit
data parameters followed by its mandatory index in the declared finite coordinate type.
Projection binder annotations never omit this wire index. Like other parameters,''')],
    'api/README.md': [
        ('''its finite arity and indexed projection signatures; these retain the exact
object parameters when a map argument is destructured. The public''',
         '''its finite arity, indexed projection and optional universal-fan witness signatures.
The exported `components.type` is the public field signature derived from the
object declaration's parameter telescope and a mandatory explicit index. It retains
the exact object parameters when a map argument is destructured. The public'''),
        ('''projection at the original object parameters followed by its typed finite index;
the ordinary full parameter-data and ownership rules apply. Framing does not''',
         '''projection at the object's explicit data parameters, omitting proofs, followed by
its typed finite index. The index remains mandatory even when the accepted projection
uses an implicit binder. The ordinary full parameter-data and ownership rules apply. Framing does not''')],
    'api/wire-examples.md': [
        ('''selector retains every explicit object declaration parameter and then the selected
index in `Fin (components.arity parameters)`:''',
         '''selector retains the object's explicit data parameters, omitting proof parameters,
and then the mandatory selected index in `Fin (components.arity parameters)`.
This is the object declaration's parameter order, regardless of the projection's
implicit-binder annotations. An implicit projection index is still required here:''')],
}


def documents():
    result = ''
    for relative, changes in DOC_CHANGES.items():
        path = CONTRACT / relative
        old = path.read_text()
        new = old
        for before, after in changes:
            new = replace_once(new, before, after)
        result += fragment(path, old, new)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--emit', action='store_true')
    parser.add_argument('--only', choices=['object', 'data', 'realize', 'docs'])
    args = parser.parse_args()
    functions = {'object': object_presentation, 'data': computational_data,
        'realize': realize, 'docs': documents}
    selected = {args.only: functions[args.only]} if args.only else functions
    body = ''.join(function() for function in selected.values())
    patch = '*** Begin Patch\n' + body + '*** End Patch\n'
    if args.emit:
        print(patch, end='')
    else:
        print(len(patch.encode()), hashlib.sha256(patch.encode()).hexdigest())
