import LeanLint

/-!
# Tests: `let` as a non-terminal tactic

`let` introduces an **abbreviation** and is treated like `have` in the discipline: it is
allowed in any non-terminal position (not just first, as `intro` is), a `--` comment may
document it, and — unlike `have` — it is *not* required to be proved with `:= by`, since its
value is an ordinary term. These tests pin that behaviour.

NOTE: descriptions are `--` comments; the only `/-- -/` on a `#guard_msgs` is its expected
message.
-/

namespace Test.Let

-- A non-terminal `let` abbreviation, used by the terminal tactic ⇒ clean.
#guard_msgs in
example : ∃ n : Nat, n = 5 := by
  let m : Nat := 5
  exact ⟨m, rfl⟩

-- A `--` comment may document a `let`, exactly as it documents a `have` ⇒ clean.
#guard_msgs in
example : ∃ n : Nat, n = 5 := by
  -- m is the chosen witness
  let m : Nat := 5
  exact ⟨m, rfl⟩

-- `let` and `have` mix freely in non-terminal position ⇒ clean.
#guard_msgs in
example (p : Prop) (h : p) : ∃ n : Nat, n = 5 ∧ p := by
  let m : Nat := 5
  -- hp restates the hypothesis
  have hp : p := by
    exact h
  exact ⟨m, rfl, hp⟩

-- Unlike `have`, a `let` needs no `:= by` proof: its value is an ordinary term ⇒ clean.
#guard_msgs in
example : ∃ n : Nat, n = 5 := by
  let m : Nat := 2 + 3
  exact ⟨m, rfl⟩

-- `let` is not restricted to the first position (that restriction is only on `intro`): here
-- it legitimately follows a `have` ⇒ clean.
#guard_msgs in
example (p : Prop) (h : p) : ∃ n : Nat, n = 5 ∧ p := by
  -- hp restates the hypothesis
  have hp : p := by
    exact h
  let m : Nat := 5
  exact ⟨m, rfl, hp⟩

-- The comment rule applies to `let` too: a comment separated from its `let` by a blank line
-- is not *immediately* above it, so it is flagged — with the message naming `have` or `let`.
/--
warning: line comment at position 64:2 must be immediately followed by a `have` or `let` tactic at the same column

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example : ∃ n : Nat, n = 5 := by
  -- m is the chosen witness

  let m : Nat := 5
  exact ⟨m, rfl⟩

end Test.Let
