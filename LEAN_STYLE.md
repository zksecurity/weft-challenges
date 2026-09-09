# Lean Style Guide

Conventions for this project’s Weft programs, functionalities, realisations,
and cost proofs.

## 1. Kernel-checked proofs

The exported development must depend only on `propext`, `Classical.choice`,
and `Quot.sound`. Do not introduce `sorryAx`, `trustCompiler`,
`Lean.ofReduceBool`, or any other axiom to discharge a proof.

Do not use `native_decide` in the development. It is allowed in `Tests/`,
which is built separately and must never be imported by `WeftChals`.
Do not disable kernel checking or replace an existing theorem with a weaker
statement to make a proof go through.

Use `decide` for small, bounded computations. Prove large statements by
composition and split expensive reductions into separately checked lemmas.
A generated plan or proposed intermediate result is untrusted data: its
relevant properties must be proved before another theorem can rely on it.
Running a generator is not evidence that its result is correct. Compiled
code may propose a certificate; the kernel must check the certificate
without a compiler-trust axiom.

Inspect `#print axioms` for the final exported declarations before calling
the development complete. A successful build alone is insufficient: Lean
also accepts files containing `sorry` with a warning.

## 2. File layout

Follow the existing separation of specifications, programs, and proofs:

```text
WeftChals/
  Spec/             -- word helpers and adapters for Wychelean
  Functionality/    -- ideal interfaces and models
  Circuit/          -- generic gadgets, plans, instances, relation lemmas
  Sem/              -- functional correctness of the generic gadgets
  Realization/      -- certified implementations, privacy, composition, cost bridges
  Timing/           -- finite timing summaries and their checked composition
  Plans/            -- generated circuit structure
  Numbers.lean      -- concrete cost and top-level realisation theorems
WeftChals.lean      -- public imports
Tests/             -- known-answer and interpreter tests
Tests.lean         -- test imports
tools/             -- generators and independent simulations
```

Keep each file focused on a gadget or a coherent group of closely related
lemmas. Put semantic helpers in `Sem/`; put the relationship between
instances in the relevant relation module. Move substantial helpers out of
`Numbers.lean`, leaving the final claims and their short composition proofs.

Keep cost and timing proofs separate from functional correctness. Generated
files in `Plans/` come from their generator; edit the generator and regenerate
the data rather than hand-editing the output.

Import only the modules needed by a file. Internal modules should not import
the root `WeftChals` module. Keep test-only dependencies out of the public
development and add public modules to the root imports as appropriate.

## 3. Namespacing and interfaces

Use `namespace WeftChals`, with focused nested namespaces such as `Word`,
`Adder`, `Compress`, and `Timing`. Use the established names rather than
introducing parallel names for the same concept.

Open `Weft` where its API is used. Keep helper names descriptive: a theorem
should indicate the operation or representation it concerns and the property
it establishes. Mark implementation-only lemmas `private` where possible.

Use named structures when several fields have distinct meanings, as in
`Compress.State`. Reuse Weft's `Shape`, `Req`, and `Resp` conventions for
functionality interfaces. State a gadget's contract through its ideal
functionality and the precondition of its realisation.

## 4. Gadgets and their realisations

### 4.1 State the functionality

Define the ideal operation and disclosure in `Functionality/`. The ideal
model states what the caller receives and what is revealed. Express its
output using the reference mathematical specification, independently of the
particular circuit plan or implementation.

State the actual precondition. Prove it at each call site; a top-level
unconditional theorem must not acquire hidden assumptions during refactoring.

### 4.2 Write the generic program

Write the gadget once over the smallest required interface: `LinM`, `BitM`,
or `WordM`. Use ordinary `do`-blocks and the project's structural `vecM`,
`listM`, and `foldM` helpers. Keep the program's operation order apparent.

Public parameters such as carry-prefix networks may select the program's
structure. Shared values must be handled through the offered operations,
not inspected as host-language values. Preserve the domain-generic nature
of the program and let Weft's `program` command certify it.

Treat reusable word operations as functionalities at the next layer.
For example, compression invokes `WordM` operations, and `Hyb` supplies the
word functionalities. Compose their realisations to obtain the Boolean
implementation. Avoid manually expanding every child program into its parent.

Keep gadgets small enough to reason about through their interfaces. Prove
correctness for every accepted plan; preserve the documented fallback
behavior for malformed plans. A plan-specific cost theorem does not justify
restricting a previously general correctness theorem to one exported plan.

### 4.3 Relate the instances

Use `Rel`, `BitRel`, and `WordRel` to connect instances of the same generic
program. Prove the primitive laws once, then lift them through each gadget
and loop. Reuse the child's relation lemma instead of unfolding the child.

The principal instances here are values, the Weft program, event logs,
and ready times with an AND count. Keep those concerns separate and compose
their proofs at the realisation boundary.

### 4.4 Prove semantics and privacy

Prove value lemmas in `Sem/`, using the children's specifications. Establish
output and view lemmas at the Weft interpreter, then use them to prove the
realisation equation. For this deterministic silent functionality, the
simulator replays the public view; do not generalise that argument to a
functionality with different disclosure or randomness without a proof.

Use `program ... : Realization ... where` for certified implementations.
Keep the `impl`, `Sim`, and `real` fields explicit. Compose implementations
with `Realizations` and `Realization.comp`, and discharge the resulting
precondition. Certification of a computable program does not itself replace
the proof of its semantics, privacy, or cost.

### 4.5 Keep proofs compositional

Before writing tactics, state the mathematical argument and identify the
intermediate lemmas. Keep existing theorem names, binders, and statements
unchanged when improving a proof.

Unfold only the layer under discussion. Prefer explicit rewrites using
the child's output, view, or timing theorem. Use small `simp only` sets
for bookkeeping; avoid simplifying a concrete expanded circuit wholesale.
Use local irreducibility where necessary to keep a child implementation
abstract, together with lemmas that expose the exact interface needed.

Do not raise heartbeat limits to compensate for an oversized proof, including
during experiments. Decompose the proof and profile it. Do not introduce
new unlimited-heartbeat regions. Existing limits are not a template for new
proofs. A local recursion-depth setting requires a concrete structural reason;
it does not resolve repeated computation or excessive memory use.

## 5. Top-level claims

`Numbers.lean` connects the exported plan to the public development:

- `timeModel_numbers`: the AND count and latest output time of the timing model.
- `compress_comm`: communication of the Boolean implementation.
- `compress_rounds`: readiness of the Boolean implementation.
- `theCircuit_real`: correctness and perfect privacy through realisation.

Derive the program's cost from the timing model through the existing
`compress_commOn` and `compress_readyOn` bridges. Derive correctness and
privacy through the composed realisation. Keep supporting encodings,
evaluation tactics, and substantial helper proofs in their own modules.

## 6. Cost and timing by composition

Prove the cost or timing of each gadget, then combine those summaries at
binds and loops. Reuse the child's checked theorem. Do not hand the kernel
one reduction of the entire expanded compression circuit.

For a concrete plan, separately checked intermediate states are also valid:
prove each transition's output and local cost, then use a generic composition
lemma to recover the original program's result. Store finite, concrete
arrival times between steps so the next proof does not expand previous steps.
Check every proposed transition against the actual timing model.

AND counts add. Exact depth also depends on the arrival times of the input
bits. Preserve the full required timing information; replacing a gadget by
a fixed scalar depth generally loses the precision needed for an exact
round-complexity theorem. Preserve constant folding and the plan's fallback
behavior in any alternative evaluator, and prove the connection.

The final theorem should combine checked facts and evaluate small arithmetic.
All certificates must retain the same kernel trust assumptions as the rest
of the development.

## 7. Profiling and validation

Profile expensive proofs before committing them. Each module must build
within 8 GB of memory. If it exceeds that budget, change the proof or its
decomposition, rather than increasing the machine's memory allocation.

Use `lake env lean path/to/File.lean` to recheck a file against built imports;
an up-to-date `lake build` measures a cache hit. Never rebuild Mathlib from
source: fetch its cache after dependency or toolchain changes.

Use `--profile` or `-Dprofiler=true` for Lean's component timings,
`-Ddiagnostics=true` for reduction counters, and `-Dtrace.profiler=true`
with `-Dtrace.profiler.output=path.json` for a Firefox Profiler trace.
Record wall time and peak resident memory. Unfolding counts are frequencies,
not CPU-time attribution, and overlapping timings must not be added together.

When kernel checking dominates while tactics take milliseconds, investigate
the expression being reduced. Look for repeated function-vector indexing,
large monadic terms, repeated list traversals, and forced unfolding of child
gadgets. The original metrics proof performed more than five million
`consFin` unfoldings for 38,656 AND gates; a tactic change alone did not
address that representation overhead.

Compare uninstrumented runs using the same toolchain, dependency artifacts,
and machine. Keep profiling output outside tracked source. After a change,
build the affected modules, then run `lake build --wfail WeftChals Tests`.
Inspect the final axioms and reject any `sorry` or added compiler-trust axiom.
