module

public import CasTools.InterfaceDocument
public meta import CasTools.InterfaceDocument
public import Lean.Elab.Command

@[expose] public section

namespace CasTools.InterfaceExport

open Lean Meta Elab Command CasCatalogue CasCompiler

syntax (name := exportInterface) "#cas_export_interface " str &"help " str : command

/-- Export the selected public registry and inert help through one explicit command.
New output files are required, so an existing publication is never overwritten. -/
@[command_elab exportInterface] meta def elabExportInterface : CommandElab := fun stx => do
  let `(command| #cas_export_interface $jsonFile:str help $helpFile:str) := stx
    | throwUnsupportedSyntax
  let jsonPath : System.FilePath := jsonFile.getString
  let helpPath : System.FilePath := helpFile.getString
  if jsonPath == helpPath || (← jsonPath.pathExists) || (← helpPath.pathExists) then
    throwError "interface export requires distinct new output files"
  let document ← liftTermElabM prepare
  let .ok rendered := help document | throwError "prepared public interface is malformed"
  let modules ← (← getEnv).header.imports.mapM fun item => do
    let path ← IO.FS.realPath (← findOLean item.module)
    return Json.mkObj [("module", NativeExpression.nameJson item.module),
      ("olean", toJson path.toString)]
  let document := document.setObjVal! "imports" (Json.arr modules)
  IO.FS.withFile jsonPath .writeNew fun jsonOutput =>
    IO.FS.withFile helpPath .writeNew fun helpOutput => do
      jsonOutput.putStrLn document.pretty
      helpOutput.putStr rendered

end CasTools.InterfaceExport
