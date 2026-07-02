import Lean

/-!
# Tactic discipline linter

A **syntax linter** that enforces a disciplined, readable shape on every `by` block:

* the **last** tactic of a sequence is *terminal* and unrestricted;
* every **earlier** (non-terminal) tactic must be `have` — with one exception:
* the **very first** tactic of the sequence may also be `intro`.
* each `by` block starts as `:= by`, with its tactics on following lines indented exactly
  two spaces past the line containing `by`;
* every `have` tactic is immediately preceded by a line comment and is proved with `:= by`.

So a well-formed block looks like an optional opening `intro`, then a run of commented
`have`s, then a single terminal tactic. An `intro` anywhere but the front, any other
non-terminal tactic (`simp`, `rw`, `constructor`, `<;>`, `·`, `case`, …), or a layout
violation is flagged.

Nested `by` blocks (e.g. the proof of a `have`) each spawn a new sequence and are checked
on their own terms, at any depth.

This is a pure-syntax linter (no `InfoTree`, no `Expr`), which is the right tool: the
notion "tactic in a `by` block" only exists at the `Syntax` level — it is erased once a
proof becomes an elaborated term in the environment, so an environment linter cannot see it.

The registration boilerplate and the parser-category trick for "is this node a tactic"
mirror Mathlib's `Mathlib/Tactic/Linter/UnusedTactic.lean`.
-/

open Lean Elab Command Linter

namespace TacticDisciplineLinter

/-- Enable the tactic discipline linter: in every `by` block, non-terminal tactics must be
`have`, except that the first tactic may also be `intro`; proof layout must follow the
readability style documented in `LeanLint/Agent.md`. -/
register_option linter.tacticDiscipline : Bool := {
  defValue := true
  descr := "non-terminal tactics must be `have` (or `intro`, as the first tactic), with disciplined proof layout"
}

/--
`SyntaxNodeKind`s of the two structuring tactics the linter cares about.

Verified against `leanprover/lean4:v4.31.0`:
  • `intro` ↦ `Lean.Parser.Tactic.intro`
  • `have`  ↦ `Lean.Parser.Tactic.tacticHave__`  (note: two trailing underscores)
-/
def introKind : Name := ``Lean.Parser.Tactic.intro
def haveKind : Name := ``Lean.Parser.Tactic.tacticHave__
def byTacticKind : Name := ``Lean.Parser.Term.byTactic

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

/-- The source text of a 1-based line, including its trailing newline if present. -/
def lineText (fmap : FileMap) (line : Nat) : String :=
  let start := fmap.lineStart line
  let stop := fmap.lineStart (line + 1)
  String.Pos.Raw.extract fmap.source start stop

/-- Count the indentation columns at the start of a line. Tabs count as one column. -/
def leadingColumns (line : String) : Nat :=
  line.toList.takeWhile (fun c => c == ' ' || c == '\t') |>.length

def isLineComment (line : String) : Bool :=
  line.trimAsciiStart.startsWith "--"

def hasCommentAbove (fmap : FileMap) (pos : Position) : Bool :=
  pos.line > 1 && isLineComment (lineText fmap (pos.line - 1))

def hasInlineAssignBy (fmap : FileMap) (byTok : Syntax) : Bool :=
  let byPos := fmap.toPosition (byTok.getPos?.getD 0)
  (lineText fmap byPos.line).contains ":= by"

def nestedByTactic? (stx : Syntax) : Option Syntax :=
  stx.find? (·.isOfKind byTacticKind)

def checkByLayout (fmap : FileMap) (byTok : Syntax) : CommandElabM Unit := do
  unless hasInlineAssignBy fmap byTok do
    let pos := fmap.toPosition (byTok.getPos?.getD 0)
    Linter.logLint linter.tacticDiscipline byTok
      m!"`by` block at position {pos.line}:{pos.column} must start as `:= by` on its declaration or `have` line"

def checkTacticIndent (fmap : FileMap) (byTok : Syntax) (t : Syntax) : CommandElabM Unit := do
  let byPos := fmap.toPosition (byTok.getPos?.getD 0)
  let pos := fmap.toPosition (t.getPos?.getD 0)
  let expected := leadingColumns (lineText fmap byPos.line) + 2
  if pos.line == byPos.line then
    Linter.logLint linter.tacticDiscipline t
      m!"tactic `{t}` found at position {pos.line}:{pos.column}; tactics in a `by` block must start on the line after `by`"
  else if pos.column != expected then
    Linter.logLint linter.tacticDiscipline t
      m!"tactic `{t}` found at position {pos.line}:{pos.column}; tactics in this `by` block must be indented exactly two spaces past the line containing `by` (expected column {expected})"

def checkHaveStyle (fmap : FileMap) (t : Syntax) : CommandElabM Unit := do
  let pos := fmap.toPosition (t.getPos?.getD 0)
  unless hasCommentAbove fmap pos do
    Linter.logLint linter.tacticDiscipline t
      m!"`have` tactic at position {pos.line}:{pos.column} must be immediately preceded by a line comment"
  if (nestedByTactic? t).isNone then
    Linter.logLint linter.tacticDiscipline t
      m!"`have` tactic at position {pos.line}:{pos.column} must use a `:= by` proof"

def checkTacticShape (tacs : Array Syntax) : CommandElabM Unit := do
  -- `tacs.pop` drops the last (terminal) tactic; everything left is non-terminal. The
  -- first non-terminal tactic (index 0) may be `intro`; all others must be `have`.
  let mut first := true
  for t in tacs.pop do
    let k := t.getKind
    let isHave := k == haveKind
    let isIntro := k == introKind
    unless isHave || (isIntro && first) do
      let pos := (← getFileMap).toPosition (t.getPos?.getD 0)
      let reason :=
        if isIntro then
          "`intro` is only allowed as the first tactic of a `by` block"
        else
          "must be `have` (or `intro`, as the first tactic)"
      Linter.logLint linter.tacticDiscipline t
        m!"non-terminal tactic `{t}` found at position {pos.line}:{pos.column}; {reason}"
    first := false

def checkByTactic (isTac : SyntaxNodeKind → Bool) (fmap : FileMap) (stx : Syntax) : CommandElabM Unit := do
  let byTok := stx.getArg 0
  let seq := stx.getArg 1
  checkByLayout fmap byTok
  let tacs := directTactics isTac seq
  for t in tacs do
    checkTacticIndent fmap byTok t
    if t.getKind == haveKind then
      checkHaveStyle fmap t
  checkTacticShape tacs

/-- Walk the whole command syntax; for every `by` block, check tactic shape and layout. -/
partial def check (isTac : SyntaxNodeKind → Bool) (fmap : FileMap) (stx : Syntax) : CommandElabM Unit := do
  if stx.isOfKind byTacticKind then
    checkByTactic isTac fmap stx
  for a in stx.getArgs do
    check isTac fmap a

/-- The linter. `withSetOptionIn` lets it see through `set_option … in` command wrappers. -/
def tacticDisciplineLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless getLinterValue linter.tacticDiscipline (← getLinterOptions) do
      return
    if (← get).messages.hasErrors then
      return
    -- Authoritative "is this node a tactic?": ask the parser for the kinds registered in
    -- the `tactic` category, rather than hard-coding a list.
    let env ← getEnv
    let cats := (Parser.parserExtension.getState env).categories
    let some tactics := Parser.ParserCategory.kinds <$> cats.find? `tactic
      | return
    check (fun k => tactics.contains k) (← getFileMap) stx

initialize addLinter tacticDisciplineLinter

end TacticDisciplineLinter
