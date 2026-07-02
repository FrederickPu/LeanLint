import LeanLint

/-!
# Tests: basic non-terminal discipline

Flat (non-nested) `by` blocks: the last tactic is terminal and unrestricted; every earlier
tactic must be `intro` or `have`.

Each `#guard_msgs` asserts the exact linter output of the wrapped example, so building this
file runs the tests. NOTE: the descriptive text for each case is a `--` line comment, never
a `/-- -/` docstring — the only docstring on a `#guard_msgs` is its expected-message string.
-/

namespace Test.Basic

-- Only `intro`/`have` in non-terminal position, arbitrary terminal tactic ⇒ clean.
#guard_msgs in
example (p : Prop) (h : p) : p → p := by
  intro _
  have hp : p := h
  exact hp

-- A single non-terminal `skip` (neither `intro` nor `have`) ⇒ one warning.
/--
warning: non-terminal tactic `skip` found at position 31:2; must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  skip
  exact h

-- The terminal tactic is unrestricted: `exact` last is fine, no warning.
#guard_msgs in
example (p : Prop) (h : p) : p := by
  exact h

-- Two non-terminal offenders ⇒ two warnings, in source order.
/--
warning: non-terminal tactic `skip` found at position 51:2; must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
---
warning: non-terminal tactic `skip` found at position 52:2; must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  skip
  skip
  exact h

-- Turning the linter off locally with `set_option … in` silences it.
#guard_msgs in
set_option linter.nonterminalDiscipline false in
example (p : Prop) (h : p) : p := by
  skip
  exact h

end Test.Basic
