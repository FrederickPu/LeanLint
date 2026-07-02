import Lean

/-!
# Non-terminal discipline linter

A **syntax linter** that flags any *non-terminal* tactic in a `by` block that is not
`intro` or `have`. "Non-terminal" is read syntactically: a tactic is non-terminal iff
it is not the last element of its tactic sequence.

This is a pure-syntax linter (no `InfoTree`, no `Expr`), which is the right tool: the
notion "tactic in a `by` block" only exists at the `Syntax` level — it is erased once a
proof becomes an elaborated term in the environment, so an environment linter cannot see it.

The registration boilerplate and the parser-category trick for "is this node a tactic"
mirror Mathlib's `Mathlib/Tactic/Linter/UnusedTactic.lean`.
-/

open Lean Elab Command Linter

namespace NonterminalLinter

/-- Enable the non-terminal discipline linter: every tactic that is not the last one in
its tactic sequence must be `intro` or `have`. -/
register_option linter.nonterminalDiscipline : Bool := {
  defValue := true
  descr := "non-terminal tactics in a `by` block must be `intro` or `have`"
}

/--
`SyntaxNodeKind`s permitted in non-terminal position.

Verified against `leanprover/lean4:v4.31.0` with `Probe.lean`:
  • `intro` ↦ `Lean.Parser.Tactic.intro`
  • `have`  ↦ `Lean.Parser.Tactic.tacticHave__`  (note: two trailing underscores)
-/
def allowedNonterminal : List Name := [
  ``Lean.Parser.Tactic.intro,        -- `intro`
  ``Lean.Parser.Tactic.tacticHave__  -- `have` (tactic mode)
]

/-- Wrapper kinds we descend *through* (they are structure, not tactics). -/
def isSeqWrapper (k : SyntaxNodeKind) : Bool :=
  k == ``Lean.Parser.Tactic.tacticSeq ||
  k == ``Lean.Parser.Tactic.tacticSeq1Indented ||
  k == ``Lean.Parser.Tactic.tacticSeqBracketed

/--
The ordered list of *direct* tactics of a tactic-sequence node.

We descend through the sequence wrappers and stop at the first tactic-category node, so a
combinator like `t₁ <;> t₂` or a focusing block `· …` is returned as a single element. We do
**not** cross into a nested `tacticSeq`; nested blocks are found and checked on their own by
the top-level walk in `check`.
-/
partial def directTactics (isTac : SyntaxNodeKind → Bool) (stx : Syntax) : Array Syntax :=
  if isTac stx.getKind && !isSeqWrapper stx.getKind then
    #[stx]
  else
    stx.getArgs.foldl (init := #[]) fun acc a =>
      if a.isOfKind ``Lean.Parser.Tactic.tacticSeq then acc
      else acc ++ directTactics isTac a

/-- Walk the whole command syntax; for every tactic sequence, check its non-terminal tactics. -/
partial def check (isTac : SyntaxNodeKind → Bool) (stx : Syntax) : CommandElabM Unit := do
  if stx.isOfKind ``Lean.Parser.Tactic.tacticSeq then
    let tacs := directTactics isTac stx
    -- `tacs.pop` drops the last (terminal) tactic; everything left is non-terminal.
    for t in tacs.pop do
      unless allowedNonterminal.contains t.getKind do
        Linter.logLint linter.nonterminalDiscipline t
          m!"non-terminal tactic must be `intro` or `have`"
  for a in stx.getArgs do
    check isTac a

/-- The linter. `withSetOptionIn` lets it see through `set_option … in` command wrappers. -/
def nonterminalDisciplineLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.nonterminalDiscipline (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    -- Authoritative "is this node a tactic?": ask the parser for the kinds registered in
    -- the `tactic` category, rather than hard-coding a list.
    let env ← getEnv
    let cats := (Parser.parserExtension.getState env).categories
    let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
      | return
    check (fun k => tactics.contains k) stx

initialize addLinter nonterminalDisciplineLinter

end NonterminalLinter
