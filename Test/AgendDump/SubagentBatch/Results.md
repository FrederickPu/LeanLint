# Batch Results

## Clean Outputs

These files import `LeanLint` and independently passed `lake env lean <file>` with no output:

- `BigPickle.lean` from `opencode/big-pickle`
- `DeepSeekV4FlashFree.lean` from `opencode/deepseek-v4-flash-free`
- `MimoV25FreeRetry.lean` from `opencode/mimo-v2.5-free`
- `Nemotron3UltraFreeRetry.lean` from `opencode/nemotron-3-ultra-free`

## Failed Or Incomplete Outputs

- `Nemotron3UltraFree.lean`: first attempt compiled, but omitted `import LeanLint`, so it did not actually exercise `linter.tacticDiscipline`.
- `NorthMiniCodeFree.lean`: first attempt omitted `import LeanLint` and failed Lean checking.
- `NorthMiniCodeFreeRetry.lean`: retry still omitted `import LeanLint` and failed Lean checking.

## Notes

- Big Pickle and DeepSeek used the linter correctly on the first attempt.
- Mimo initially wrote to the wrong path and omitted the linter import, but the retry succeeded cleanly in the requested dump folder.
- Nemotron initially omitted the linter import, but the retry succeeded cleanly.
- North repeatedly struggled with Windows PowerShell syntax and Lean proof repair, so it did not demonstrate reliable linter use.
