# Subagent Batch

This folder contains a fresh batch of model/agent proof-generation tests against the stricter `LeanLint/Agent.md` proof style.

Each model was asked to:

- Read/use `LeanLint/Agent.md`.
- Write one Lean file in this folder.
- Import `LeanLint`.
- Generate readable proofs with comments above each `have`, `:= by` on `have` lines, no same-line terminal automation, and exact one-step indentation.
- Run `lake env lean` on its own file and fix any `linter.tacticDiscipline` warnings.

See `Results.md` for pass/fail status.
