import LeanLint

/-!
# Tests: nested `have` blocks

The interesting behaviour of the linter is that a `have` whose proof is itself a `by`
block spawns a *new* tactic sequence, and that inner sequence is checked on its own terms:
its own last tactic is terminal, everything before it must be `intro`/`have`.

Each `#guard_msgs` asserts the exact set of linter warnings the wrapped example produces,
so building this file runs the tests. We use `skip` as the canonical "disallowed,
goal-preserving" non-terminal tactic: unlike `simp`/`trivial` it never closes the goal, so
it never introduces a "no goals" error that would (correctly) suppress the linter.

NOTE: descriptions are `--` comments; the only `/-- -/` on a `#guard_msgs` is its expected
message.
-/

namespace Test.Nested

-- A `have` may sit in non-terminal position in the outer block (that is the whole point),
-- and if its inner proof is clean the example is clean.
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have h2 : p := h
  exact h2

-- Inner block has a non-terminal `skip` ⇒ exactly one warning, reported inside the
-- `have`'s proof, not on the `have` itself.
/--
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have h2 : p := by
    skip
    exact h
  exact h2

-- Three levels of nested `have`, every level clean (only `have` + terminal `exact`)
-- ⇒ no warnings, no matter how deep.
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have a : p := by
    have b : p := by
      have c : p := h
      exact c
    exact b
  exact a

-- Non-terminal `skip` in the outer block AND in the inner block ⇒ two independent
-- warnings; nesting does not mask either one.
/--
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
---
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  skip
  have h2 : p := by
    skip
    exact h
  exact h2

-- `intro` and `have` may be freely mixed in non-terminal position at any depth: here the
-- inner `by` block legitimately opens with `intro` (its goal is a function type).
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have h2 : p → p := by
    intro hp
    have hp' : p := hp
    exact hp'
  exact h2 h

-- A non-terminal `skip` buried one level deeper than a clean outer `have` is still
-- caught: the outer block is clean, but the innermost block is not.
/--
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have outer : p := by
    have inner : p := by
      skip
      exact h
    exact inner
  exact outer

end Test.Nested
