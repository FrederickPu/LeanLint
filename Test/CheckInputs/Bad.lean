namespace Test.CheckInputs.Bad

example (p : Prop) (h : p) : p := by
  have hp : p := by exact h
  exact hp

end Test.CheckInputs.Bad
