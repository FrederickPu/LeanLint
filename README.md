# LeanLint

A Lean 4 **syntax linter** enforcing *tactic discipline* and readable proof layout: every
tactic in a `by` block that is not the last one in its sequence must be `have` — with a
single exception, the **very first** tactic may also be `intro`. Everything else — `simp`,
`rw`, `constructor`, `<;>`, focusing dots `·`, `case`, … — is only allowed in *terminal*
(last) position, and an `intro` anywhere but the front is flagged too.

The layout is intentionally strict too: `by` blocks start as `:= by`, tactics begin on the
following line, tactic bodies are indented exactly two spaces past the line containing
`by`, and every `have` has a `--` comment immediately above it plus its own `:= by` proof.

So a disciplined block reads as an optional opening `intro`, then a run of commented
`have`s, then one terminal tactic.

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

**Positive sample** (clean — an opening `intro`, then `have`, then a terminal tactic):

```lean
import LeanLint

example (p : Prop) (h : p) : p → p := by
  intro hp            -- first tactic → `intro` allowed here
  -- hp' is the introduced proof of p
  have hp' : p := by  -- non-terminal, but `have`  → allowed
    exact hp
  exact hp'           -- terminal → anything goes
```

**Negative sample — wrong tactic** (`simp` is non-terminal and not a `have`):

```lean
import LeanLint

example : True := by
  simp     -- ⚠️ warning: non-terminal tactic `simp` found at position …; must be `have` (or `intro`, as the first tactic)
  trivial  -- terminal → fine
```

**Negative sample — misplaced `intro`** (`intro` is only allowed as the first tactic):

```lean
import LeanLint

example (p q : Prop) (h : p) : q → p := by
  -- hp is the given proof of p
  have hp : p := by
    exact h
  intro _  -- ⚠️ warning: `intro` is only allowed as the first tactic of a `by` block
  exact hp
```

**Negative sample — layout** (`have` needs a comment above it, and automation cannot sit on
the `:= by` line):

```lean
import LeanLint

example (p : Prop) (h : p) : p := by
  have hp : p := by exact h  -- ⚠️ warning: missing comment and same-line tactic
  exact hp
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
```

The [`Test`](./Test) library is the test suite: each case wraps an `example` in
`#guard_msgs`, so a mismatch between expected and actual linter output fails the build. It
is a default target, so plain `lake build` — including CI — runs it.
