# Writing proofs that pass LeanLint

Your goal is to write Lean 4 proofs that are **human-readable** and that pass the
`linter.tacticDiscipline` linter provided by this package.

## The discipline

The linter enforces a fixed shape on every `by` block:

- The **last** tactic of a block is *terminal* and unrestricted — use whatever automation
  closes the goal (`exact`, `simp`, `omega`, `decide`, `constructor <;> …`, …).
- Every **earlier** (non-terminal) tactic must be `have` or `let` (both introduce a binding:
  `have` an assumption, `let` an abbreviation).
- The **only** exception: the very first tactic of a block may be `intro`.
- Every `by` block must start as `:= by` on the declaration or `have` line.
- The first tactic after `by` must be on the next line, never on the `:= by` line.
- Tactics inside a `by` block must be indented exactly two spaces past the `have`/`let`/
  declaration that owns the block; do not double-indent proof bodies. (If a `have`'s statement
  wraps across several lines, the body is still measured against the `have`, not the wrapped
  `by` line.)
- Every `have` proof itself must use `:= by`. A `let` needs no `:= by` — its value is an
  ordinary term (`let m : Nat := 5`).
- Comments are optional, but every `--` comment inside a proof block must be a standalone
  line immediately followed by a `have` or `let` tactic at the same indentation. Do not put
  trailing comments after tactics, and do not comment `intro` or the terminal tactic.

So a well-formed block is an optional opening `intro`, then a run of commented `have`s and
`let`s, then a single closing tactic. Nested `by` blocks (each `have`'s proof) are checked
the same way, at every depth.

## How to write the proof

1. First think of the most sensible **informal** proof.
2. Turn each informal step into a `have` whose statement is that step's conclusion.
   Comments are optional; when you include one, put it as a standalone `--` comment on the
   line immediately above the `have`, aligned to the `have`.
3. If the goal opens with hypotheses to introduce, do it with a single leading `intro` (it
   may take several names: `intro a b hab`). Introduce everything up front, not mid-proof.
4. Write every `have` proof as `:= by` on the `have` line, then put the terminal tactic on
   the next line indented exactly two more spaces. Do not write `:= by exact ...` on one
   line.
5. Close every `have`'s proof — and the final goal — with **terminal** automation: the last
   tactic of each block does the work.
6. Verify generated files with `lake exe leanlint-check path/to/File.lean`. This enables
   LeanLint even if the file itself does not import it.

## Example

```lean
example (a b : Nat) (h : a = b) : a + 1 = b + 1 := by
  -- rewriting a to b makes both sides equal
  have key : a + 1 = b + 1 := by
    rw [h]
  exact key
```

## Anti-patterns the linter will flag

- A non-`have`, non-terminal tactic mid-proof: `simp` / `rw` / `constructor` before the
  last line. Fold that work into a `have` or move it to terminal position.
- An `intro` that is not the first tactic (e.g. a `have` before it). Hoist all `intro`s to
  the front.
- A comment in a proof block that is not immediately above an aligned `have` or `let`.
- A trailing comment after a tactic, including after `have ... := by`.
- A `have` proved by a bare term (`:= h`) or with `by` on the next line. Use `:= by` on the
  `have` line.
- A tactic on the same line as `by`, such as `:= by exact ...`.
- A tactic indented more or less than exactly two spaces past the line containing its `by`.
