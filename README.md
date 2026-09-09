# Weft SHA-256

A SHA-256 compression circuit over secret-shared bits, built with
[Weft](https://github.com/zksecurity/weft). Lean proofs establish:

- Correctness against [Wychelean](https://github.com/rozbb/wychelean)’s compression function
- Perfect privacy
- 38,656 AND gates and 456 rounds, with all input bits available at round zero

The main results are in [Numbers.lean](WeftChals/Numbers.lean).
The circuit works for arbitrary chaining values and message blocks.

## Building

Uses Lean 4.34.0-rc2 and a Weft checkout at `../weft`.
Wychelean and Mathlib are pinned in `lakefile.toml`.

```
lake exe cache get
lake build --wfail WeftChals Tests
```

See [LEAN_STYLE.md](LEAN_STYLE.md) for proof conventions.
