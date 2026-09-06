import WeftChals.Circuit.BitM

/-!
# Bitwise word gadgets: choice, majority, carry-save compression

Each is one AND per bit (before folding); the carry-save compressor drops
the carry out of bit 31, so its carry word has a constant `false` at bit
0, which later gadgets fold.
-/
namespace WeftChals

universe u
variable {m : Type → Type u} [Monad m] {S : Type} [BitM m S]

namespace Word

/-- `Ch(x, y, z)`, bitwise. -/
def ch (x y z : Word S) : m (Word S) := vecM 32 fun i => Bit.ch3 (x i) (y i) (z i)

/-- `Maj(x, y, z)`, bitwise. -/
def maj (x y z : Word S) : m (Word S) := vecM 32 fun i => Bit.maj3 (x i) (y i) (z i)

/-- The bit below `i`, when there is one. -/
def below (w : Word S) (i : Fin 32) : Bit S :=
  if h : i.val = 0 then .const false else w ⟨i.val - 1, by omega⟩

/-- 3:2 carry-save compression modulo `2^32`: `x + y + z ≡ s + c`.  The
carry word is the majority shifted up by one; its bit 0 is `false` and
the carry out of bit 31 is dropped. -/
def csa3 (x y z : Word S) : m (Word S × Word S) := do
  let s ← vecM 32 fun i => do
    let t ← Bit.xor (x i) (y i)
    Bit.xor t (z i)
  let c ← vecM 32 fun i =>
    if h : i.val = 0 then pure (.const false)
    else Bit.maj3 (x ⟨i.val - 1, by omega⟩) (y ⟨i.val - 1, by omega⟩) (z ⟨i.val - 1, by omega⟩)
  pure (s, c)

end Word

end WeftChals
