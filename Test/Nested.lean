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
  -- h2 is the original proof of p
  have h2 : p := by
    exact h
  exact h2

-- Inner block has a non-terminal `skip` ⇒ exactly one warning, reported inside the
-- `have`'s proof, not on the `have` itself.
/--
warning: non-terminal tactic `skip` found at position 41:4; must be `have` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- h2 follows from the original proof of p
  have h2 : p := by
    skip
    exact h
  exact h2

-- Three levels of nested `have`, every level clean (only `have` + terminal `exact`)
-- ⇒ no warnings, no matter how deep.
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- a follows from a nested proof of p
  have a : p := by
    -- b follows from a deeper nested proof of p
    have b : p := by
      -- c is the original proof of p
      have c : p := by
        exact h
      exact c
    exact b
  exact a

-- Non-terminal `skip` in the outer block AND in the inner block ⇒ two independent
-- warnings; nesting does not mask either one.
/--
warning: non-terminal tactic `skip` found at position 73:2; must be `have` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
---
warning: non-terminal tactic `skip` found at position 76:4; must be `have` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  skip
  -- h2 follows from the original proof of p
  have h2 : p := by
    skip
    exact h
  exact h2

-- `intro` and `have` may be freely mixed in non-terminal position at any depth: here the
-- inner `by` block legitimately opens with `intro` (its goal is a function type).
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- h2 is the identity function on p
  have h2 : p → p := by
    intro hp
    -- hp' is the introduced proof of p
    have hp' : p := by
      exact hp
    exact hp'
  exact h2 h

-- A non-terminal `skip` buried one level deeper than a clean outer `have` is still
-- caught: the outer block is clean, but the innermost block is not.
/--
warning: non-terminal tactic `skip` found at position 106:6; must be `have` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- outer follows from an inner proof of p
  have outer : p := by
    -- inner follows from the original proof of p
    have inner : p := by
      skip
      exact h
    exact inner
  exact outer

end Test.Nested
