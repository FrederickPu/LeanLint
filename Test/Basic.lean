import LeanLint

/-!
# Tests: basic non-terminal discipline

Flat (non-nested) `by` blocks: the last tactic is terminal and unrestricted; every earlier
tactic must be `have` or `let` (or `intro`, as the first tactic).

Each `#guard_msgs` asserts the exact linter output of the wrapped example, so building this
file runs the tests. NOTE: the descriptive text for each case is a `--` line comment, never
a `/-- -/` docstring — the only docstring on a `#guard_msgs` is its expected-message string.
-/

namespace Test.Basic

-- Only `intro`/`have` in non-terminal position, arbitrary terminal tactic ⇒ clean.
#guard_msgs in
example (p : Prop) (h : p) : p → p := by
  intro _
  -- hp is the original proof of p
  have hp : p := by
    exact h
  exact hp

-- A single non-terminal `skip` (neither `intro` nor `have`) ⇒ one warning.
/--
warning: non-terminal tactic `skip` found at position 33:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
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
warning: non-terminal tactic `skip` found at position 53:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
---
warning: non-terminal tactic `skip` found at position 54:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  skip
  skip
  exact h

-- Turning the linter off locally with `set_option … in` silences it.
#guard_msgs in
set_option linter.tacticDiscipline false in
example (p : Prop) (h : p) : p := by
  skip
  exact h

-- `intro` is allowed only as the *very first* tactic. Here a `have` occupies first
-- position, so the following `intro` is out of place and is flagged — with the dedicated
-- "`intro` only as the first tactic" message, not the generic one.
/--
warning: non-terminal tactic `intro _` found at position 77:2; `intro` is only allowed as the first tactic of a `by` block

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p q : Prop) (h : p) : q → p := by
  -- hp is the original proof of p
  have hp : p := by
    exact h
  intro _
  exact hp

-- Only the first tactic may be `intro`: a second, immediately-following `intro` is
-- non-terminal-but-not-first, so it too is flagged.
/--
warning: non-terminal tactic `intro _` found at position 90:2; `intro` is only allowed as the first tactic of a `by` block

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p q : Prop) (h : p) : p → q → p := by
  intro _
  intro _
  exact h

end Test.Basic
