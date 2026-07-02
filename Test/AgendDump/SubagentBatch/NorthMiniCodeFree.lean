namespace Test.AgendDump.SubagentBatch.NorthMiniCodeFree

example (a b c : Nat) (hab : a = b) (hbc : b = c) : a + 1 = c + 1 := by
  -- prove a = c using transitivity of equality
  have ac : a = c := by
    rw [hab, hbc]
  rw [ac]

example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> r := by
  -- transitivity of implication from p to r
  have pr : p -> r := by
    intro hp
    have hq : q := by
      exact hpq hp
    exact hqr hq
  exact pr

example (p q : Prop) (hp : p) (hq : q) : q /\ p := by
  -- swap the order of the conjunction, proving both components separately
  have qp : q /\ p := by
    constructor
    · exact hq
    · exact hp
  exact qp

example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> q /\ r := by
  -- prove both q and r from p using the implications
  have qr : q /\ r := by
    intro hp
    have hq : q := by
      exact hpq hp
    have hr : r := by
      have hq2 : q := by
        exact hq
      exact hqr hq2
    constructor
    · exact hq
    · exact hr
  exact qr

example (p q : Prop) (h : p /\ q) : q /\ p := by
  -- swap the propositions in the conjunction
  have pq_swap : q /\ p := by
    cases h with hp hq
    constructor
    · exact hq
    · exact hp
  exact pq_swap