/-!
# A writer monad for pure circuit models

The pure models of a circuit (its AND depth and count, its view) are
computed in a writer monad whose accumulator is combined *hierarchically*
along the program's structure: `x >>= k` adds the two contributions.
A state threaded through every gate would instead build a term chain as
long as the circuit, which the kernel cannot evaluate; a writer sum is
as deep as the program's nesting, not its length.
-/
namespace WeftChals

/-- An accumulator: a zero and an associative combination. -/
class Acc (ω : Type) where
  zero : ω
  app : ω → ω → ω

instance : Acc Nat := ⟨0, (· + ·)⟩
instance {α : Type} : Acc (List α) := ⟨[], (· ++ ·)⟩

/-- The writer monad over an accumulator. -/
def Writer (ω : Type) (α : Type) : Type := α × ω

namespace Writer
variable {ω : Type} [Acc ω]

def pure {α : Type} (a : α) : Writer ω α := (a, Acc.zero)

def bind {α β : Type} (x : Writer ω α) (k : α → Writer ω β) : Writer ω β :=
  match k x.1 with
  | (b, w) => (b, Acc.app x.2 w)

instance : Monad (Writer ω) where
  pure := Writer.pure
  bind := Writer.bind

@[simp] theorem bind_eq {α β : Type} (x : Writer ω α) (k : α → Writer ω β) : x >>= k = Writer.bind x k := rfl
@[simp] theorem pure_eq {α : Type} (a : α) : (Pure.pure a : Writer ω α) = Writer.pure a := rfl
@[simp] theorem pure_fst {α : Type} (a : α) : (Writer.pure a : Writer ω α).1 = a := rfl
@[simp] theorem pure_snd {α : Type} (a : α) : (Writer.pure a : Writer ω α).2 = Acc.zero := rfl
@[simp] theorem bind_fst {α β : Type} (x : Writer ω α) (k : α → Writer ω β) : (Writer.bind x k).1 = (k x.1).1 := rfl
@[simp] theorem bind_snd {α β : Type} (x : Writer ω α) (k : α → Writer ω β) :
    (Writer.bind x k).2 = Acc.app x.2 (k x.1).2 := rfl

end Writer

/-- Writer over a count: the accumulator is `ℕ` under addition. -/
abbrev Count := Writer Nat
/-- Writer over a log: the accumulator is a list under append. -/
abbrev Log (ε : Type) := Writer (List ε)

@[simp] theorem Acc.nat_zero : (Acc.zero : Nat) = 0 := rfl
@[simp] theorem Acc.nat_app (a b : Nat) : Acc.app a b = a + b := rfl
@[simp] theorem Acc.list_zero {α : Type} : (Acc.zero : List α) = [] := rfl
@[simp] theorem Acc.list_app {α : Type} (a b : List α) : Acc.app a b = a ++ b := rfl

end WeftChals
