/-!
# Circuit plans

The structure of the low-depth SHA-256 circuit is data: which carry-save
compressions happen in which order, and which carry-prefix network each
adder uses.  The Python generator chooses these by timing-driven search
and exports them; the Lean circuit consumes them.  Every consumer is
total and correct for *every* plan (ill-formed plans fall back to a
ripple structure), so correctness never depends on the data.  Cost does,
and is decided for the exported plans.

Encodings are packed naturals so that the generated files elaborate fast.
-/
namespace WeftChals

/-- A carry-prefix network on `n` elements (element `k` is a bit
position), as productions in emission order.  A production is packed as
`isG * 32768 + a * 1024 + b * 32 + m` with `a ≤ m < b < 32`:

* `isG = 1`: `G[a..b]` from `G[m+1..b] ⊕ (P[m+1..b] ∧ G[a..m])`, or, when
  `m + 1 = b`, `maj (x b) (y b) G[a..m]` (one AND, no `g b`/`p b`).
* `isG = 0`: `P[a..b]` from `P[m+1..b] ∧ P[a..m]`.

Leaves `G[a..a] = x a ∧ y a` and `P[a..a] = x a ⊕ y a` are implicit. -/
structure Net where
  n : Nat
  prods : List Nat
  deriving DecidableEq, Repr

/-- One decoded production. -/
structure Prod where
  isG : Bool
  a : Nat
  b : Nat
  m : Nat
  deriving DecidableEq, Repr

def Prod.decode (c : Nat) : Prod :=
  ⟨c / 32768 % 2 = 1, c / 1024 % 32, c / 32 % 32, c % 32⟩

/-- A multi-operand sum: carry-save steps on a shrinking operand list,
each packed `i * 64 + j * 8 + k` (positions in the *current* list; the
three are removed and the sum and shifted-carry words appended), then a
network for the final two-operand addition. -/
structure SumPlan where
  csa : List Nat
  net : Net
  deriving DecidableEq, Repr

/-- One decoded carry-save step. -/
def SumPlan.decodeStep (c : Nat) : Nat × Nat × Nat := (c / 64 % 8, c / 8 % 8, c % 8)

/-- One compression round.  With `base = some p`, the early words
`h + K[t] + W[t]` are resolved once by `p` and shared by the two sums;
otherwise they are compressed once by a carry-save step and the pair is
shared. -/
structure RoundPlan where
  base : Option SumPlan
  newA : SumPlan
  newE : SumPlan
  deriving Repr

/-- A whole compression: 48 schedule sums, 64 rounds, 8 feed-forward networks. -/
structure BlockPlan where
  schedule : List SumPlan
  rounds : List RoundPlan
  final : List Net
  deriving Repr

end WeftChals
