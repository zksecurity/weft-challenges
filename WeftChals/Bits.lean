import Weft
import WeftChals.Spec.Bitwise

/-!
# 32-bit words of `𝔽₂` bits, and their meaning

A word is a function `Fin 32 → GF2`, least significant bit first.  `toNat`
reads it as a number, `ofNat` writes one; the word operations below are
the ideal models of the word functionalities.
-/
namespace WeftChals
open Weft

/-- A 32-bit word of bits, least significant first. -/
abbrev Word32 := Fin 32 → GF2

namespace Word32

/-- The number with the given `n` low bits, least significant first. -/
def toNatAux : (n : Nat) → (Fin n → GF2) → Nat
  | 0, _ => 0
  | n + 1, w => (w 0).val + 2 * toNatAux n fun i => w i.succ

/-- The number a word denotes. -/
def toNat (w : Word32) : Nat := toNatAux 32 w

/-- The word as a fixed-width integer. -/
def toUInt32 (w : Word32) : UInt32 := (toNat w).toUInt32

/-- The word of a number (its 32 low bits). -/
def ofNat (n : Nat) : Word32 := bitsOf 32 n

/-- `Ch`, bitwise: `z ⊕ x(y ⊕ z)`. -/
def ch (x y z : Word32) : Word32 := fun i => z i + x i * (y i + z i)

/-- `Maj`, bitwise: `xy ⊕ xz ⊕ yz`. -/
def maj (x y z : Word32) : Word32 := fun i => x i * y i + x i * z i + y i * z i

/-- The sum word of a carry-save compression. -/
def csaSum (x y z : Word32) : Word32 := fun i => x i + y i + z i

/-- The carry word of a carry-save compression: the majority, shifted up. -/
def csaCarry (x y z : Word32) : Word32 := fun i =>
  if h : i.val = 0 then 0 else maj x y z ⟨i.val - 1, by omega⟩

/-- Addition modulo `2^32`. -/
def add (x y : Word32) : Word32 := ofNat (add32 (toNat x) (toNat y))

/-- The sum of a list of words modulo `2^32`. -/
def sumList (ws : List Word32) : Word32 := ofNat ((ws.map toNat).sum % 2 ^ 32)

end Word32

end WeftChals
