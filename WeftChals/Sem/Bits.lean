import WeftChals.Bits
import WeftChals.Spec.SHA256

/-!
# Words as numbers

`Word32.toNat` reads a word as a number; the lemmas here say how the
bitwise word operations read: as the specification's operations on
numbers below `2^32`.
-/
namespace WeftChals
open Weft

namespace Word32

theorem toNat_lt (w : Word32) : toNat w < 2 ^ 32 := by sorry

theorem testBit_toNat (w : Word32) (i : Nat) (hi : i < 32) :
    (toNat w).testBit i = GF2.toBool (w ⟨i, hi⟩) := by sorry

theorem testBit_toNat_of_ge (w : Word32) (i : Nat) (hi : 32 ≤ i) : (toNat w).testBit i = false := by sorry

@[simp] theorem ofNat_apply (n : Nat) (i : Fin 32) : ofNat n i = GF2.ofBool (n.testBit i) := rfl

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n % 2 ^ 32 := by sorry

theorem ofNat_toNat (w : Word32) : ofNat (toNat w) = w := by sorry

theorem ext_toNat {x y : Word32} (h : toNat x = toNat y) : x = y := by
  rw [← ofNat_toNat x, ← ofNat_toNat y, h]

theorem toNat_xor (x y : Word32) : toNat (fun i => x i + y i) = toNat x ^^^ toNat y := by sorry

theorem toNat_and (x y : Word32) : toNat (fun i => x i * y i) = toNat x &&& toNat y := by sorry

theorem toNat_ch (x y z : Word32) : toNat (ch x y z) = Specs.SHA256.Ch (toNat x) (toNat y) (toNat z) := by sorry

theorem toNat_maj (x y z : Word32) : toNat (maj x y z) = Specs.SHA256.Maj (toNat x) (toNat y) (toNat z) := by sorry

theorem toNat_rotr (x : Word32) (n : Nat) :
    toNat (fun i => x ⟨(i.val + n) % 32, Nat.mod_lt _ (by decide)⟩) = rotRight32 (toNat x) n := by sorry

theorem toNat_shr (x : Word32) (n : Nat) :
    toNat (fun i => if h : i.val + n < 32 then x ⟨i.val + n, h⟩ else 0) = toNat x / 2 ^ n := by sorry

theorem toNat_add (x y : Word32) : toNat (add x y) = add32 (toNat x) (toNat y) := by
  simp only [add, toNat_ofNat, add32, Nat.mod_mod]

/-- Carry-save compression preserves the sum modulo `2^32`. -/
theorem csa_sum (x y z : Word32) :
    (toNat (csaSum x y z) + toNat (csaCarry x y z)) % 2 ^ 32 = (toNat x + toNat y + toNat z) % 2 ^ 32 := by sorry

theorem toNat_sumList (ws : List Word32) : toNat (sumList ws) = (ws.map toNat).sum % 2 ^ 32 := by
  simp only [sumList, toNat_ofNat, Nat.mod_mod]

end Word32

end WeftChals
