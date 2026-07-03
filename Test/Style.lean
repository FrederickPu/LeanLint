import LeanLint

/-!
# Tests: proof readability layout

These cases pin down the human-readable proof layout enforced on top of the basic tactic
discipline: `have`s need comments, `have` proofs need `:= by`, tactics start after `by`,
comments must sit immediately above aligned `have`s, and tactic bodies are indented exactly
one step.

NOTE: descriptions are `--` comments; the only `/-- -/` on a `#guard_msgs` is its expected
message.
-/

namespace Test.Style

-- A `have` without a preceding explanatory comment is allowed.
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have hp : p := by
    exact h
  exact hp

-- A trailing comment on the `have` line is not enough; the comment must be above it.
/--
warning: line comment at position 32:20 must be immediately followed by a `have` tactic at the same column

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  have hp : p := by -- hp is the original proof of p
    exact h
  exact hp

-- A blank line between the comment and `have` is not immediate, so it is flagged.
/--
warning: line comment at position 44:2 must be immediately followed by a `have` tactic at the same column

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- hp is the original proof of p

  have hp : p := by
    exact h
  exact hp

-- A block comment is ignored by the line-comment formatting rule.
#guard_msgs in
example (p : Prop) (h : p) : p := by
  /- hp is the original proof of p -/
  have hp : p := by
    exact h
  exact hp

-- The comment must be aligned to the `have` it documents.
/--
warning: line comment at position 66:4 must be immediately followed by a `have` tactic at the same column

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
    -- hp is the original proof of p
  have hp : p := by
    exact h
  exact hp

-- A proof-block comment must document a `have`, not a terminal tactic.
/--
warning: line comment at position 79:2 must be immediately followed by a `have` tactic at the same column

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- this comment is above the terminal tactic, not a have
  exact h

-- A `have` proved by a bare term is flagged; use `:= by` instead.
/--
warning: `have` tactic at position 91:2 must use a `:= by` proof

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- hp is the original proof of p
  have hp : p := h
  exact hp

-- A `by` on the line after `:=` is flagged; write `:= by` on the `have` line.
/--
warning: `by` block at position 104:4 must start as `:= by` on its declaration or `have` line

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
warning: tactic `exact h` found at position 117:20; tactics in a `by` block must start on the line after `by`

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
  h` found at position 131:6; tactics in this `by` block must be indented exactly two spaces past the line containing `by` (expected column 4)

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
warning: tactic `trivial` found at position 141:21; tactics in a `by` block must start on the line after `by`

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example : True := by trivial

-- Top-level tactic bodies must use exactly one indentation step.
/--
warning: tactic `trivial` found at position 151:4; tactics in this `by` block must be indented exactly two spaces past the line containing `by` (expected column 2)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example : True := by
    trivial

end Test.Style
