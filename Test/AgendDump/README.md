# Agent Dump

`LeanLint/Agent.md` was used as the proof-writing instruction source.

## Files

- `DeepSeekV4FlashFree.lean`: proof output from the available `opencode/deepseek-v4-flash-free` model, saved as Lean source with Markdown fences stripped and namespace/end normalized for the dump path.
- `DeepSeekV3Probe.md`: exact DeepSeek V3 probe result. No proof was generated because the requested model was not available.
- `Qwen3Probe.md`: exact Qwen 3 probe result. No proof was generated because no Qwen model/provider was configured.
- `Prompt.md`: shared prompt used for the successful proof-generation run.

## Quick Readability Note

The DeepSeek-family proof is generally readable and now follows the enforced comment-above-`have`, inline-`:= by`, and fixed-indentation layout.
