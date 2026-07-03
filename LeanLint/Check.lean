import LeanLint

open System

namespace LeanLint.Check

def usage : String :=
  "usage: lake exe leanlint-check <file.lean>"

def wrapperPath (path : FilePath) : FilePath :=
  path.withFileName s!"{path.fileName.getD "input.lean"}.leanlint-check.lean"

def runLean (path : FilePath) : IO UInt32 := do
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["--error=warning", path.toString]
  }
  unless out.stdout.isEmpty do
    IO.print out.stdout
  unless out.stderr.isEmpty do
    (← IO.getStderr).putStr out.stderr
  if out.exitCode != 0 then
    return out.exitCode
  else if out.stdout.contains "warning:" || out.stdout.contains "error:" ||
      out.stderr.contains "warning:" || out.stderr.contains "error:" then
    return 1
  else
    return 0

def checkFile (path : FilePath) : IO UInt32 := do
  unless (← path.pathExists) do
    (← IO.getStderr).putStrLn s!"leanlint-check: file not found: {path}"
    return 2
  let source ← IO.FS.readFile path
  let wrapped := "import LeanLint\n" ++ source
  let wrapper := wrapperPath path
  if (← wrapper.pathExists) then
    (← IO.getStderr).putStrLn s!"leanlint-check: temporary wrapper already exists: {wrapper}"
    return 2
  try
    IO.FS.writeFile wrapper wrapped
    let code ← runLean wrapper
    try
      IO.FS.removeFile wrapper
    catch _ =>
      pure ()
    return code
  catch e =>
    try
      if (← wrapper.pathExists) then
        IO.FS.removeFile wrapper
    catch _ =>
      pure ()
    throw e

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] => checkFile ⟨path⟩
  | _ =>
    (← IO.getStderr).putStrLn usage
    return 2

end LeanLint.Check

def main (args : List String) : IO UInt32 :=
  LeanLint.Check.main args
