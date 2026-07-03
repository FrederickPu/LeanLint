import Lean

/-!
# Tests: `lake exe leanlint-check`

These tests exercise the CLI helper through `IO.Process.output`. The input files do not
import `LeanLint`; the checker should enable it through its temporary wrapper.
-/

open Lean Elab Command System

namespace Test.Check

def cleanFile : String := "Test/CheckInputs/Clean.lean"
def badFile : String := "Test/CheckInputs/Bad.lean"

def runChecker (file : String) : IO IO.Process.Output :=
  IO.Process.output {
    cmd := "lake"
    args := #["exe", "leanlint-check", file]
  }

def combinedOutput (out : IO.Process.Output) : String :=
  out.stdout ++ out.stderr

def assertNoWrapper (file : String) : CommandElabM Unit := do
  let wrapper : FilePath := ⟨file ++ ".leanlint-check.lean"⟩
  if ← wrapper.pathExists then
    throwError m!"leanlint-check left temporary wrapper behind: {wrapper}"

run_cmd
  let out ← runChecker cleanFile
  if out.exitCode != 0 then
    throwError m!"leanlint-check should accept {cleanFile}, exit={out.exitCode}\n{combinedOutput out}"
  assertNoWrapper cleanFile

run_cmd
  let out ← runChecker badFile
  if out.exitCode == 0 then
    throwError m!"leanlint-check should reject {badFile}, but exited 0"
  unless (combinedOutput out).contains "tactics in a `by` block must start on the line after `by`" do
    throwError m!"leanlint-check rejected {badFile}, but did not report the expected linter warning\n{combinedOutput out}"
  assertNoWrapper badFile

end Test.Check
