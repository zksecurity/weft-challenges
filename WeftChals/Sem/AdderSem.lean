import WeftChals.Sem.Bits
import WeftChals.Sem.Value

/-!
# Carries, semantically

`G x y a k` is the carry out of adding bits `a..a+k` of two words with no
carry in; `P x y a k` says every position there propagates.  The split
laws are what a carry-prefix network computes; the `BitVec` bridge says
the carry chain is addition.
-/
namespace WeftChals
open Weft

namespace AdderSem

/-- Bit `i` of a word (modulo `32`, so that positions are plain naturals). -/
def bit (w : Word32) (i : Nat) : GF2 := w ⟨i % 32, Nat.mod_lt _ (by decide)⟩

@[simp] theorem bit_lt (w : Word32) (i : Nat) (h : i < 32) : bit w i = w ⟨i, h⟩ := by
  simp [bit, Nat.mod_eq_of_lt h]

variable (x y : Word32)

/-- Generate. -/
def g (i : Nat) : GF2 := bit x i * bit y i
/-- Propagate. -/
def p (i : Nat) : GF2 := bit x i + bit y i
/-- Majority. -/
def maj (a b c : GF2) : GF2 := a * b + a * c + b * c

/-- `G[a..a+k]`, by the majority recursion. -/
def G (a : Nat) : Nat → GF2
  | 0 => g x y a
  | k + 1 => maj (bit x (a + k + 1)) (bit y (a + k + 1)) (G a k)

/-- `P[a..a+k]`. -/
def P (a : Nat) : Nat → GF2
  | 0 => p x y a
  | k + 1 => p x y (a + k + 1) * P a k

theorem maj_eq (a b c : GF2) : maj a b c = a * b + (a + b) * c := by
  simp only [maj]; ring

theorem G_succ (a k : Nat) : G x y a (k + 1) = g x y (a + k + 1) + p x y (a + k + 1) * G x y a k := by
  rw [G, maj_eq]; rfl

theorem G_split (a k : Nat) : ∀ j, G x y a (k + j + 1) = G x y (a + k + 1) j + P x y (a + k + 1) j * G x y a k
  | 0 => by rw [Nat.add_zero, G_succ]; rfl
  | j + 1 => by
    rw [show k + (j + 1) + 1 = (k + j + 1) + 1 by omega, G_succ, G_split a k j, G_succ, P]
    rw [show a + (k + j + 1) + 1 = a + k + 1 + j + 1 by omega]
    ring

theorem P_split (a k : Nat) : ∀ j, P x y a (k + j + 1) = P x y (a + k + 1) j * P x y a k
  | 0 => by rw [Nat.add_zero, P]; rfl
  | j + 1 => by
    rw [show k + (j + 1) + 1 = (k + j + 1) + 1 by omega, P, P_split a k j, P]
    rw [show a + (k + j + 1) + 1 = a + k + 1 + j + 1 by omega]
    ring

/-- With no generate below `k`, the low carries vanish. -/
theorem G_zero_of_g_zero (a k : Nat) (h : ∀ i, i ≤ a + k → g x y i = 0) : ∀ j, j ≤ k → G x y a j = 0
  | 0, _ => by rw [G]; exact h a (by omega)
  | j + 1, hj => by
    rw [G_succ, G_zero_of_g_zero a k h j (by omega), h (a + j + 1) (by omega)]
    ring

/-! ## The carry chain is addition -/

/-- A word as a bit-vector. -/
def bv (w : Word32) : BitVec 32 := BitVec.ofNat 32 (Word32.toNat w)

theorem getLsbD_bv (w : Word32) (i : Nat) (hi : i < 32) : (bv w).getLsbD i = GF2.toBool (w ⟨i, hi⟩) := by
  rw [bv, BitVec.getLsbD_ofNat, Word32.testBit_toNat w i hi]
  simp [hi]

theorem toBool_maj (a b c : GF2) : GF2.toBool (maj a b c) = Bool.atLeastTwo (GF2.toBool a) (GF2.toBool b) (GF2.toBool c) := by
  revert a b c; decide

theorem carry_eq : ∀ i, i < 31 → BitVec.carry (i + 1) (bv x) (bv y) false = GF2.toBool (G x y 0 i)
  | 0, _ => by
    rw [BitVec.carry_succ, BitVec.carry_zero, G, g, getLsbD_bv _ 0 (by decide), getLsbD_bv _ 0 (by decide),
      GF2.toBool_mul]
    simp [Bool.atLeastTwo, bit]
  | i + 1, h => by
    rw [BitVec.carry_succ, carry_eq i (by omega), G, toBool_maj, getLsbD_bv _ _ (by omega), getLsbD_bv _ _ (by omega)]
    simp [bit, Nat.mod_eq_of_lt (show i + 1 < 32 by omega)]

/-- Bit `i` of the sum: the propagate and the carry in. -/
theorem add_bit (i : Nat) (hi : i < 32) :
    Word32.add x y ⟨i, hi⟩ = bit x i + bit y i + (if i = 0 then 0 else G x y 0 (i - 1)) := by
  rw [Word32.add, Word32.ofNat_apply, add32]
  have h1 : (Word32.toNat x + Word32.toNat y) % 2 ^ 32 = (bv x + bv y).toNat := by
    rw [BitVec.toNat_add, bv, bv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Word32.toNat_lt x),
      Nat.mod_eq_of_lt (Word32.toNat_lt y)]
  rw [h1]
  have h2 : (bv x + bv y).toNat.testBit i = (bv x + bv y).getLsbD i := rfl
  rw [h2, BitVec.getLsbD_add hi, getLsbD_bv _ i hi, getLsbD_bv _ i hi, GF2.ofBool_xor, GF2.ofBool_xor,
    GF2.ofBool_toBool, GF2.ofBool_toBool, bit_lt _ _ hi, bit_lt _ _ hi]
  cases i with
  | zero => simp [BitVec.carry_zero]
  | succ i =>
    rw [carry_eq x y i (by omega), GF2.ofBool_toBool]
    simp [add_assoc]

end AdderSem

end WeftChals
