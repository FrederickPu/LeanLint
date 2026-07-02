import LeanLint

/-!
# Tests: structuring / combinator tactics ("and stuff")

The rule is deliberately strict: *only* `intro` and `have` are allowed in non-terminal
position. Structuring tactics — focusing dots `·`, `case`, `<;>`, `refine`, `constructor`,
… — are therefore flagged when they are not the last tactic of their sequence. These tests
pin that behaviour down so a future relaxation (adding kinds to `allowedNonterminal`) is a
visible, deliberate change.

NOTE: descriptions are `--` comments; the only `/-- -/` on a `#guard_msgs` is its expected
message.
-/

namespace Test.Structuring

-- `refine` (non-terminal) and the first focusing dot are flagged; the last dot is
-- terminal and is not. ⇒ two warnings.
/--
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
---
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example : True ∧ True := by
  refine ⟨?_, ?_⟩
  · trivial
  · trivial

-- A `<;>` combinator that is itself the terminal tactic is unrestricted ⇒ clean.
#guard_msgs in
example : True ∧ True := by
  constructor <;> trivial

-- `constructor` and a non-terminal `<;>` combinator are both flagged; the final `exact`
-- is terminal. ⇒ two warnings.
/--
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
---
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : (True ∧ True) ∧ p := by
  constructor
  constructor <;> trivial
  exact h

-- `constructor` and a non-terminal `case` block are both flagged; the trailing `trivial`
-- is terminal. ⇒ two warnings.
/--
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
---
warning: non-terminal tactic must be `intro` or `have`

Note: This linter can be disabled with `set_option linter.nonterminalDiscipline false`
-/
#guard_msgs in
example : True ∧ True := by
  constructor
  case left => trivial
  trivial

end Test.Structuring
