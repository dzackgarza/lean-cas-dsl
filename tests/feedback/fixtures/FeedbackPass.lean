module

#eval show IO Unit from do
  let output := IO.FS.Stream.ofHandle (← IO.FS.Handle.mk "/proc/self/fd/1" .write)
  output.putStrLn "feedback passing module entered"
  output.flush
  let hold : System.FilePath := "feedback-record-hold"
  if ← hold.pathExists then
    IO.FS.writeFile "feedback-record-ready" "feedback passing module entered\n"
    while ← hold.pathExists do
      IO.sleep 10
  output.putStrLn "feedback passing module finished"
  output.flush
