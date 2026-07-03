import LeanLint

/-!
# Tests: term-mode `by` blocks

A `by` written inline in a term — `f (by omega)`, `⟨by simp, …⟩` — is *term mode*: unlike the
`:= by` proof of a declaration or a `have`, it is not held to the full layout/shape
discipline, but it *must* contain a single tactic. So `(by trivial)` is fine, while
`(by skip; trivial)` is a tactic sequence in term position and is flagged.

Each `#guard_msgs` asserts the exact linter output of the wrapped example, so building this
file runs the tests.

NOTE: descriptions are `--` comments; the only `/-- -/` on a `#guard_msgs` is its expected
message.
-/

namespace Test.TermMode

-- A single-tactic term-mode `by` argument is fine ⇒ clean.
#guard_msgs in
example (f : True → True) : True :=
  f (by trivial)

-- A term-mode `by` holding a `;` tactic sequence is flagged.
/--
warning: term-mode `by` block at position 33:5 must contain a single tactic; a tactic sequence like `by t₁; t₂` is not allowed in term position

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (f : True → True) : True :=
  f (by skip; trivial)

-- The single-tactic rule holds however the sequence is laid out — newlines, not just `;`.
/--
warning: term-mode `by` block at position 43:5 must contain a single tactic; a tactic sequence like `by t₁; t₂` is not allowed in term position

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (f : True → True) : True :=
  f (by
    skip
    trivial)

-- In an anonymous constructor each `by` is its own term-mode block: the first (a single
-- tactic) is clean, the second (a sequence) is flagged.
/--
warning: term-mode `by` block at position 56:15 must contain a single tactic; a tactic sequence like `by t₁; t₂` is not allowed in term position

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example : True ∧ True :=
  ⟨by trivial, by skip; trivial⟩

-- Turning the linter off silences the term-mode rule too.
#guard_msgs in
set_option linter.tacticDiscipline false in
example (f : True → True) : True :=
  f (by skip; trivial)

-- Proof-mode discipline is unaffected: a clean `:= by` `have` proof produces no warning even
-- with term-mode `by`s elsewhere in the file.
#guard_msgs in
example (p : Prop) (h : p) : p := by
  -- hp is the original proof of p
  have hp : p := by
    exact h
  exact hp

end Test.TermMode
