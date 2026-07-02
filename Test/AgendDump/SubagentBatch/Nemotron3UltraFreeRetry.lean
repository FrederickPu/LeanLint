import LeanLint

namespace Test.AgendDump.SubagentBatch.Nemotron3UltraFreeRetry

example (a b c : Nat) (hab : a = b) (hbc : b = c) : a + 1 = c + 1 := by
  -- rewriting a to b and b to c makes both sides equal
  have h_ac : a = c := by
    rw [hab, hbc]
  -- rewriting a to c makes both sides equal
  have h_main : a + 1 = c + 1 := by
    rw [h_ac]
  exact h_main

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by
  intro hp
  -- applying hpq to hp gives q
  have hq : q := by
    exact hpq hp
  -- applying hqr to hq gives r
  have hr : r := by
    exact hqr hq
  exact hr

example (p q : Prop) (hp : p) (hq : q) : q ∧ p := by
  -- q is true by assumption
  have hq' : q := by
    exact hq
  -- p is true by assumption
  have hp' : p := by
    exact hp
  -- combine q and p to get q ∧ p
  have h_main : q ∧ p := by
    exact ⟨hq', hp'⟩
  exact h_main

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → q ∧ r := by
  intro hp
  -- applying hpq to hp gives q
  have hq : q := by
    exact hpq hp
  -- applying hqr to hq gives r
  have hr : r := by
    exact hqr hq
  -- combine q and r to get q ∧ r
  have h_main : q ∧ r := by
    exact ⟨hq, hr⟩
  exact h_main

example (p q : Prop) (h : p ∧ q) : q ∧ p := by
  -- q is true by the right part of the conjunction
  have hq : q := by
    exact h.2
  -- p is true by the left part of the conjunction
  have hp : p := by
    exact h.1
  -- combine q and p to get q ∧ p
  have h_main : q ∧ p := by
    exact ⟨hq, hp⟩
  exact h_main

end Test.AgendDump.SubagentBatch.Nemotron3UltraFreeRetry