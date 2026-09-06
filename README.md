# weft-chals: SHA-256 compression over secret-shared bits

A verified low-AND-depth SHA-256 compression function on secret-shared
`GF(2)` bits, in [weft](../weft), with machine-checked round complexity,
communication (AND count), correctness against the golf specification,
and perfect privacy.

## What is here

| Piece | Where |
|---|---|
| The SHA-256 specification (copied from golf, checked by its test vectors) | `WeftChals/Spec/` |
| The Python circuit generators (unchanged) and the plan exporter | `sha256_lowdepth_v2.py`, `prefix_dp.py`, `tools/` |
| The exported circuit structure (prefix networks, compression orders) | `WeftChals/Plans/Compression.lean` |
| The functionality `SHA256Compress` and the word functionalities | `WeftChals/Functionality/` |
| The generic circuit kit and the gadgets | `WeftChals/Circuit/` |
| Correctness of the gadgets and of the compression program | `WeftChals/Sem/` |
| The realisations and the cost theorems | `WeftChals/Realization/`, `WeftChals/Numbers.lean` |
| Known-answer tests (`native_decide`, outside the development) | `Tests/` |

## The functionality

`SHA256Compress` (`WeftChals/Functionality/Compress.lean`): one operation
on a shared chaining value (8 words) and a shared block (16 words), each
word 32 shared bits least significant first; it returns
`Specs.SHA256.compressBlock` of the two, as shared words.  It declares no
disclosure.

The compression function is written against *word functionalities*
(`WeftChals/Functionality/Word.lean`): `Ch32`, `Maj32`, `Csa3`
(carry-save compression), `Add32` and `Sum32` (modular addition of two
words, and of a list of words).  `Add32` and `Sum32` take the structure
of their circuit (a carry-prefix network, a compression plan) as the
operation, so a caller chooses the circuit per call while the meaning
stays the sum.

## The Boolean hybrid

`Bool2 := [Lin GF2, Mult GF2]` (weft's `Weft/Std/Boolean.lean`): xor is
free, an AND costs one round and one unit of communication, so `delayOn`
is AND depth and `commOn` the AND count.  The word functionalities are
realised over `Bool2` by bit-level gadgets; the compression function is
realised over the hybrid of the word functionalities; weft's composition
theorem gives the compression function over `Bool2`.

## The circuit

The circuit is the one `sha256_lowdepth_v2.py --mode compression`
generates: carry-save trees in arrival order, deadline-driven carry-prefix
adders, the early words `h + K[t] + W[t]` shared between the two round
sums.  Its structure is data (`BlockPlan`, `WeftChals/Circuit/Plan.lean`),
exported by `tools/plan_export.py` and consumed by the Lean gadgets, which
are total and correct for every plan; the cost is decided for the exported
one.  Word interfaces carry plain shares, so the generator's constant
folding across an interface (the fixed-IV specialisation, 455 rounds) is
not reproduced; inside a gadget it is.

Gadgets are written once, over a monad offering xor, and and constants
(`WeftChals/Circuit/BitM.lean`).  Instantiated at weft's free monad they
are the certified program; at `Id` the pure function the correctness
proof reasons about; at a counting writer on ready times the timing model
the kernel evaluates.  One relation lemma per gadget connects them
(`WeftChals/Circuit/Rel.lean`).

## The theorems

For the exported plan (`WeftChals/Numbers.lean`):

* `compress_rounds`: the output of the composed program is ready at round 456.
* `compress_comm`: it communicates 38656 units (one per AND).
* `theCircuit_real`: the realisation equation, for every request: output
  is `compressBlock`, view is simulated from the event alone (perfect
  privacy); it is `Realization.comp` of the certificates checked by weft's
  `program` command.

Both cost theorems are the timing model's numbers, decided by the kernel
(`decide +kernel`), transported to the weft program by the relation
lemmas and `Realizations.sched_timed`.

## Building

```
lake exe cache get
lake build
```

`Tests` uses `native_decide`; the development does not.  Regenerate the
plan with `python3 tools/plan_export.py` (writes
`WeftChals/Plans/Compression.lean` and `tools/plan_compression.json`);
`python3 tools/lean_model.py tools/plan_compression.json` re-simulates the
plan under the Lean rules and prints the same numbers.
