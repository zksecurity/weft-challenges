import WeftChals.Circuit.Csa
import WeftChals.Circuit.Adder

/-!
# Multi-operand sums modulo `2^32`

Carry-save compression in the order the plan says, on a shrinking list of
operands, then one carry-prefix addition.  Steps that name positions that
do not exist are skipped, and whatever is left beyond two operands is
compressed in a fixed order, so the sum is right for every plan.
-/
namespace WeftChals

universe u
variable {m : Type → Type u} [Monad m] {S : Type} [BitM m S]

namespace Sum32

/-- One carry-save step on the operand list. -/
def step (ws : List (Word S)) (code : Nat) : m (List (Word S)) :=
  let d := SumPlan.decodeStep code
  let i := d.1
  let j := d.2.1
  let k := d.2.2
  if i < ws.length ∧ j < ws.length ∧ k < ws.length ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k then do
    let hi := max i (max j k)
    let lo := min i (min j k)
    let mid := i + j + k - hi - lo
    let rest := ((ws.eraseIdx hi).eraseIdx mid).eraseIdx lo
    let r ← Word.csa3 (ws.getD i (Word.const 0)) (ws.getD j (Word.const 0)) (ws.getD k (Word.const 0))
    pure (rest ++ [r.1, r.2])
  else pure ws

/-- Reduce to at most two operands (fixed order), then add. -/
def finish (net : Net) (fuel : Nat) : List (Word S) → m (Word S)
  | [] => pure (Word.const 0)
  | [x] => pure x
  | [x, y] => Adder.add net x y
  | x :: y :: z :: rest =>
    match fuel with
    | 0 => pure x
    | fuel + 1 => do
      let r ← Word.csa3 x y z
      finish net fuel (rest ++ [r.1, r.2])

/-- The sum of the operands modulo `2^32`, as the plan structures it. -/
def sum (plan : SumPlan) (ws : List (Word S)) : m (Word S) := do
  let ws ← foldM step ws plan.csa
  finish plan.net ws.length ws

end Sum32

end WeftChals
