# DeepSeek V3 Probe

Requested model: DeepSeek V3.

Attempted model ID: `opencode/deepseek-v3-free`.

Result: no proof was generated. The configured OpenCode account only exposed `opencode/deepseek-v4-flash-free` as a DeepSeek-family model, and the V3 probe failed before producing output.

```text
! agent "general" is a subagent, not a primary agent. Falling back to default agent
Error:
Error: {
  "name": "UnknownError",
  "data": {
    "message": "Unexpected server error. Check server logs for details.",
    "ref": "err_1b6ed88e"
  }
}
```
