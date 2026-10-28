import Lake

open System Lake

def main (arguments : List String) : IO UInt32 := do
  let paths : List String ← match arguments with
    | [manifest] => do
        let contents ← IO.FS.readFile manifest
        pure ((contents.splitOn "\n").filter (fun item => !item.isEmpty))
    | paths => pure paths
  for argument in paths do
    let path : FilePath := argument
    IO.println s!"{(← Lake.computeBinFileHash path).hex} {argument}"
  return 0
