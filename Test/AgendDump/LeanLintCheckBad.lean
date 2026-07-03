namespace Test.AgendDump.LeanLintCheckBad

example (p : Prop) (h : p) : p := by
  have hp : p := by exact h
  exact hp

end Test.AgendDump.LeanLintCheckBad
