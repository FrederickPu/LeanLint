# Proof Generation Prompt

Instructions were attached from `LeanLint/Agent.md`.

```text
Use the attached Agent.md instructions. Return only raw Lean 4 source, no Markdown fences or explanation. Include import LeanLint and namespace Test.AgentDump.DeepSeek. Generate readable proofs for these examples: example (a b c : Nat) (hab : a = b) (hbc : b = c) : a + 1 = c + 1 := by ...; example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> r := by ...; example (p q : Prop) (hp : p) (hq : q) : q /\ p := by ...; example (p q r : Prop) (hpq : p -> q) (hqr : q -> r) : p -> q /\ r := by .... Follow Agent.md: optional first intro, then have steps with concise comments immediately above each have, each have proof written as `:= by`, and one terminal tactic per by block on the next line with exactly one extra indentation step. Do not use sorry, admit, or disable linters. Do not edit files or run tools.
```
