namespace Test.AgendDump.LeanLintCheckClean

example (p : Prop) (h : p) : p := by
  have hp : p := by
    exact h
  exact hp

end Test.AgendDump.LeanLintCheckClean
