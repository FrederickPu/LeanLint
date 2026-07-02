namespace Test.AgendDump.SubagentBatch.NorthMiniCodeFreeRetry

example (a b c : Nat) (hab : a = b) (hbc : b = c) : a + 1 = c + 1 := by
  -- derive a = c from the chain of equalities, then use congruence of + with 1
  have ac : a = c := by
    rw [hab, hbc]
  have ac_plus1 : a + 1 = c + 1 := by
    rw [ac]
    congr_add
  exact ac_plus1

example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> r := by
  -- transitivity of implication: if p then q, and q then r, thus p then r
  have pr : p -> r := by
    intro hp
    have hq : q := by
      exact hpq hp
    have hr : r := by
      exact hqr hq
    exact hr
  exact pr

example (p q : Prop) (hp : p) (hq : q) : q /\ p := by
  -- swap the order of the conjunction
  have pq_swap : q /\ p := by
    constructor
    · exact hq
    · exact hp
  exact pq_swap

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