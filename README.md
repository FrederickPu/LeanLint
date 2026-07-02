# LeanLint

A Lean 4 **syntax linter** enforcing *non-terminal discipline*: every tactic in a `by`
block that is not the last one in its sequence must be `intro` or `have`. Everything
else — `simp`, `rw`, `constructor`, `<;>`, focusing dots `·`, `case`, … — is only allowed
in *terminal* (last) position.

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

**Positive sample** (clean — the only non-terminal tactics are `intro` and `have`):

```lean
import LeanLint

example (p : Prop) (h : p) : p → p := by
  intro hp        -- non-terminal, but `intro`  → allowed
  have hp' : p := hp  -- non-terminal, but `have`  → allowed
  exact hp'       -- terminal → anything goes
```

**Negative sample** (flagged — `simp` is non-terminal and is neither `intro` nor `have`):

```lean
import LeanLint

example : True := by
  simp     -- ⚠️ warning: non-terminal tactic `simp` found at position …; must be `intro` or `have`
  trivial  -- terminal → fine
```

Turn it off (globally, or locally with `in`):

```lean
set_option linter.nonterminalDiscipline false in
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
