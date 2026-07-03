# Shared Batch Prompt

```text
Use LeanLint/Agent.md as the binding proof-writing guide. Create exactly one Lean source file at the specified target path. Only touch that target file.

Use the namespace specified in the prompt. The file may omit `import LeanLint` because the checker enables it. Generate readable Lean 4 proofs for these examples:

1. example (a b c : Nat) (hab : a = b) (hbc : b = c) : a + 1 = c + 1 := by ...
2. example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> r := by ...
3. example (p q : Prop) (hp : p) (hq : q) : q /\ p := by ...
4. example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> q /\ r := by ...
5. example (p q : Prop) (h : p /\ q) : q /\ p := by ...

Follow the updated linter style strictly:

- Each by block starts as := by on the declaration or have line.
- No tactic is on the same line as by.
- Tactics are indented exactly two spaces past the line containing by.
- Comments are optional, but any -- proof-block comment must be immediately above an aligned have.
- Every have proof uses := by.
- Earlier non-terminal tactics are have only, except the first tactic may be intro.
- Do not use sorry, admit, or disable linters.

After writing the file, run lake exe leanlint-check on that exact file. If it reports any warning or Lean error, fix the file and rerun. In your final response, report the file path and the final leanlint-check result.
```
