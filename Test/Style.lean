import LeanLint

/-!
# Tests: proof readability layout

These cases pin down the human-readable proof layout enforced on top of the basic tactic
discipline: `have`s need comments, `have` proofs need `:= by`, tactics start after `by`,
and tactic bodies are indented exactly one step.

NOTE: descriptions are `--` comments; the only `/-- -/` on a `#guard_msgs` is its expected
message.
-/

namespace Test.Style

-- A `have` without a preceding explanatory comment is flagged.
/--
warning: `have` tactic at position 24:2 must be immediately preceded by a line comment

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have hp : p := by
    exact h
  exact hp

-- A `have` proved by a bare term is flagged; use `:= by` instead.
/--
warning: `have` tactic at position 37:2 must use a `:= by` proof

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- hp is the original proof of p
  have hp : p := h
  exact hp

-- A `by` on the line after `:=` is flagged; write `:= by` on the `have` line.
/--
warning: `by` block at position 50:4 must start as `:= by` on its declaration or `have` line

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- hp is the original proof of p
  have hp : p :=
    by
      exact h
  exact hp

-- Terminal automation on the same line as `by` is flagged.
/--
warning: tactic `exact h` found at position 63:20; tactics in a `by` block must start on the line after `by`

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- hp is the original proof of p
  have hp : p := by exact h
  exact hp

-- A nested proof body with two extra indentation steps is flagged.
/--
warning: tactic `exact
  h` found at position 77:6; tactics in this `by` block must be indented exactly two spaces past the line containing `by` (expected column 4)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- hp is the original proof of p
  have hp : p := by
      exact h
  exact hp

-- Top-level terminal automation on the same line as `by` is also flagged.
/--
warning: tactic `trivial` found at position 87:21; tactics in a `by` block must start on the line after `by`

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example : True := by trivial

-- Top-level tactic bodies must use exactly one indentation step.
/--
warning: tactic `trivial` found at position 97:4; tactics in this `by` block must be indented exactly two spaces past the line containing `by` (expected column 2)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example : True := by
    trivial

end Test.Style
