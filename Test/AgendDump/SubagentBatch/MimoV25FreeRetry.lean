import LeanLint

namespace Test.AgendDump.SubagentBatch.MimoV25FreeRetry

example (a b c : Nat) (hab : a = b) (hbc : b = c) : a + 1 = c + 1 := by
  -- a equals c by transitivity of equality
  have ac : a = c := by
    rw [hab, hbc]
  -- adding 1 to both sides preserves equality
  have goal : a + 1 = c + 1 := by
    omega
  exact goal

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  -- q follows from p via hpq
  have hq : q := by
    exact hpq hp
  -- r follows from q via hqr
  have hr : r := by
    exact hqr hq
  exact hr

example (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  -- construct q ∧ p by swapping the order of the hypotheses
  have conj : q ∧ p := by
    exact And.intro hq hp
  exact conj

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → q ∧ r := by
  intro hp
  -- q follows from p via hpq
  have hq : q := by
    exact hpq hp
  -- r follows from q via hqr
  have hr : r := by
    exact hqr hq
  -- combine q and r into the conjunction
  have conj : q ∧ r := by
    exact And.intro hq hr
  exact conj

example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  -- extract p from the left side of the conjunction
  have hp : p := by
    exact h.1
  -- extract q from the right side of the conjunction
  have hq : q := by
    exact h.2
  -- construct q ∧ p by swapping the order
  have conj : q ∧ p := by
    exact And.intro hq hp
  exact conj

end Test.AgendDump.SubagentBatch.MimoV25FreeRetry
