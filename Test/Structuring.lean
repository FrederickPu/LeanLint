import LeanLint

/-!
# Tests: structuring / combinator tactics ("and stuff")

The rule is deliberately strict: in non-terminal position only `have` is allowed (plus
`intro`, but only as the first tactic). Structuring tactics — focusing dots `·`, `case`,
`<;>`, `refine`, `constructor`, … — are therefore flagged when they are not the last tactic
of their sequence. These tests pin that behaviour down so a future relaxation is a visible,
deliberate change.

NOTE: descriptions are `--` comments; the only `/-- -/` on a `#guard_msgs` is its expected
message.
-/

namespace Test.Structuring

-- `refine` (non-terminal) and the first focusing dot are flagged; the last dot is
-- terminal and is not. ⇒ two warnings.
/--
warning: non-terminal tactic `refine ⟨?_, ?_⟩` found at position 31:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
---
warning: non-terminal tactic `· trivial` found at position 32:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
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
warning: non-terminal tactic `constructor` found at position 54:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
---
warning: non-terminal tactic `constructor <;>
  trivial` found at position 55:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example (p : Prop) (h : p) : (True ∧ True) ∧ p := by
  constructor
  constructor <;> trivial
  exact h

-- `constructor` and a non-terminal `case` block are both flagged; the trailing `trivial`
-- is terminal. ⇒ two warnings.
/--
warning: non-terminal tactic `constructor` found at position 72:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
---
warning: non-terminal tactic `case left =>
  trivial` found at position 73:2; must be `have` or `let` (or `intro`, as the first tactic)

Note: This linter can be disabled with `set_option linter.tacticDiscipline false`
-/
#guard_msgs in
example : True ∧ True := by
  constructor
  case left => trivial
  trivial

end Test.Structuring
