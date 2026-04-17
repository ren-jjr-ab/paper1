# scev-demo

Companion to: **"is lim sin(x)/x = 1, == 1, or ~= 1?"** (Section 4.1.1)

Same program + different budget = different tokens + different result.

## Usage

```
cargo run              # uses cases.json (default)
cargo run -- my.json   # uses custom config
```

## Config format

`cases.json` defines programs and budgets:

```json
{
  "cases": [
    {
      "name": "...",
      "description": "...",
      "program": { "type": "collatz", "start": 27 },
      "budgets": [
        { "max_bits": 16, "max_intervals": 4, "max_steps": 200 }
      ]
    }
  ]
}
```

### Program types

| Type | Fields | Description |
|------|--------|-------------|
| `collatz` | `start` | Collatz sequence from `start`, exits at 1 |
| `infinite` | `init`, `stride` | Infinite loop: `b += stride` |
| `concrete` | `init`, `stride`, `exit_at` | Finite loop: `c += stride`, exits at step `exit_at` |
| `limit` | `scale` | Fixed-point `sin(x)/x` as `x -> 0`, precision = `scale` |

### Budget parameters

| Parameter | Meaning |
|-----------|---------|
| `max_bits` | Bit width of representable values (overflow = Unknown) |
| `max_intervals` | Capacity of the interval set (exceeding triggers merge = information destruction) |
| `max_steps` | Maximum evaluation steps (exhaustion = Unknown) |

## Output

Each run prints per-step traces showing the interval set state,
merge count, phantom values (information lost to merging), and memory usage.

**Merges** = interval destructions. Each merge is one act of information loss.
**Phantoms** = values fabricated by merging (never actually observed).
