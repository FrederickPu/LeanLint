import LeanLint

namespace Test.AgendDump.SubagentBatch.BigPickle

example (a b c : Nat) (hab : a = b) (hbc : b = c) : a + 1 = c + 1 := by
  -- a = c by transitivity
  have ac : a = c := by
    exact Eq.trans hab hbc
  -- rewriting a to c makes both sides equal
  have goal : a + 1 = c + 1 := by
    rw [ac]
  exact goal

example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> r := by
  intro hp
  -- q follows from hp
  have hq : q := by
    exact hpq hp
  -- r follows from hq
  have hr : r := by
    exact hqr hq
  exact hr

example (p q : Prop) (hp : p) (hq : q) : q /\ p := by
  -- conjunction from the hypotheses
  have conj : q /\ p := by
    exact And.intro hq hp
  exact conj

example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> q /\ r := by
  intro hp
  -- q follows from hp
  have hq : q := by
    exact hpq hp
  -- r follows from hq
  have hr : r := by
    exact hqr hq
  -- conjunction of hq and hr
  have conj : q /\ r := by
    exact And.intro hq hr
  exact conj

example (p q : Prop) (h : p /\ q) : q /\ p := by
  -- extract p from the hypothesis
  have hp : p := by
    exact h.left
  -- extract q from the hypothesis
  have hq : q := by
    exact h.right
  -- swap the conjunction
  have conj : q /\ p := by
    exact And.intro hq hp
  exact conj

end Test.AgendDump.SubagentBatch.BigPickle
