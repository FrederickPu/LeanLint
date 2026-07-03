# LeanLint

A Lean 4 **syntax linter** enforcing *tactic discipline* and readable proof layout: every
tactic in a `by` block that is not the last one in its sequence must be `have` or `let` (both
introduce a binding) — with a single exception, the **very first** tactic may also be
`intro`. Everything else — `simp`, `rw`, `constructor`, `<;>`, focusing dots `·`, `case`, …
— is only allowed in *terminal* (last) position, and an `intro` anywhere but the front is
flagged too.

The layout is intentionally strict too: `by` blocks start as `:= by`, tactics begin on the
following line, tactic bodies are indented exactly two spaces past the `have`/`let`/declaration
that owns the block (so a `have` whose statement wraps across several lines is still measured
against the `have`, not the wrapped `by` line), and every `have` has its own `:= by` proof.
Comments are optional, but any `--` comment inside a proof block must be a standalone line
immediately followed by a `have` or `let` at the same indentation.

So a disciplined block reads as an optional opening `intro`, then a run of commented `have`s
and `let`s, then one terminal tactic.

Those rules govern *proof* `by` blocks — the `:= by` value of a declaration or of a `have`.
A **term-mode** `by`, written inline in a term (`f (by omega)`, `⟨by simp, …⟩`), is instead
held to a single rule: it must contain exactly **one** tactic. So `(by omega)` is fine, but a
tactic sequence like `(by split; omega; omega)` in term position is flagged.

Nested `by` blocks (e.g. the proof of a `have`) are each checked on their own terms, at any
depth.

Toolchain: `leanprover/lean4` as pinned in [`lean-toolchain`](./lean-toolchain).

## Use as a dependency

Add to your `lakefile.toml`:

```toml
[[require]]
name = "LeanLint"
git = "https://github.com/FrederickPu/LeanLint"   # or your fork
rev = "master"
```

Then, in any file, just import it — the linter registers itself on import and runs on the
rest of the file.

Or, to check a file without editing it to import `LeanLint`, run:

```sh
lake exe leanlint-check path/to/File.lean
```

This helper creates a temporary wrapper beside the target file, prepends `import LeanLint`,
runs Lean, prints any output, and removes the wrapper. It exits nonzero if Lean reports an
error or warning.

**Positive sample** (clean — an opening `intro`, then `have`, then a terminal tactic):

```lean
import LeanLint

example (p : Prop) (h : p) : p → p := by
  intro hp
  -- hp' is the introduced proof of p
  have hp' : p := by
    exact hp
  exact hp'
```

**Positive sample — `let`** (an abbreviation is non-terminal like `have`, needs no `:= by`):

```lean
import LeanLint

example : ∃ n : Nat, n = 5 := by
  -- m is the chosen witness
  let m : Nat := 5
  exact ⟨m, rfl⟩
```

**Negative sample — wrong tactic** (`simp` is non-terminal and not a `have`):

```lean
import LeanLint

example : True := by
  simp
  trivial
```

**Negative sample — misplaced `intro`** (`intro` is only allowed as the first tactic):

```lean
import LeanLint

example (p q : Prop) (h : p) : q → p := by
  -- hp is the given proof of p
  have hp : p := by
    exact h
  intro _
  exact hp
```

**Negative sample — layout** (automation cannot sit on the `:= by` line):

```lean
import LeanLint

example (p : Prop) (h : p) : p := by
  have hp : p := by exact h
  exact hp
```

**Comment placement** (comments are optional, but if present they must be standalone,
aligned with, and directly above a `have`):

```lean
import LeanLint

example (p : Prop) (h : p) : p := by
  -- hp is the given proof of p
  have hp : p := by
    exact h
  exact hp
```

These are flagged:

```lean
import LeanLint

example (p : Prop) (h : p) : p := by
  have hp : p := by -- trailing comments do not document the have
    exact h
  exact hp

example (p : Prop) (h : p) : p := by
    -- this comment is not aligned with the have
  have hp : p := by
    exact h
  exact hp

example (p : Prop) (h : p) : p := by
  -- this comments the terminal tactic, not a have
  exact h
```

**Negative sample — term-mode sequence** (an inline `by` may hold only one tactic):

```lean
import LeanLint

example (f : True → True) : True :=
  f (by skip; trivial)
```

Turn it off (globally, or locally with `in`):

```lean
set_option linter.tacticDiscipline false in
example : True := by simp; trivial
```

## Develop / test

```sh
lake build          # build the library and run the test suite
lake build LeanLint # library only
lake build Test     # tests only
lake exe leanlint-check path/to/File.lean # check one file with LeanLint enabled
```

The [`Test`](./Test) library is the test suite: each case wraps an `example` in
`#guard_msgs`, so a mismatch between expected and actual linter output fails the build. It
is a default target, so plain `lake build` — including CI — runs it.
