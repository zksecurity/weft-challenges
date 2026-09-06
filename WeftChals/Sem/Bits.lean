import WeftChals.Bits
import WeftChals.Spec.SHA256
import Mathlib.Algebra.BigOperators.Fin

/-!
# Words as numbers

`Word32.toNat` reads a word as a number; the lemmas here say how the
bitwise word operations read: as the specification's operations on
numbers below `2^32`.
-/
namespace WeftChals
open Weft

namespace Word32

theorem toNatAux_lt : ∀ (n : Nat) (w : Fin n → GF2), toNatAux n w < 2 ^ n
  | 0, _ => by simp [toNatAux]
  | n + 1, w => by
    simp only [toNatAux]
    have h1 := ZMod.val_lt (w 0)
    have h2 := toNatAux_lt n fun i => w i.succ
    rw [Nat.pow_succ]
    omega

theorem toBool_val_mod (c : GF2) : decide (c.val % 2 = 1) = GF2.toBool c := by
  revert c; decide

theorem testBit_toNatAux : ∀ (n : Nat) (w : Fin n → GF2) (i : Nat),
    (toNatAux n w).testBit i = if h : i < n then GF2.toBool (w ⟨i, h⟩) else false
  | 0, _, i => by simp [toNatAux]
  | n + 1, w, 0 => by
    simp only [toNatAux, Nat.testBit_zero, Nat.zero_lt_succ, dite_true]
    rw [Nat.add_mul_mod_self_left, toBool_val_mod]
    rfl
  | n + 1, w, i + 1 => by
    simp only [toNatAux, Nat.testBit_succ]
    have hv := ZMod.val_lt (w 0)
    have e : ((w 0).val + 2 * toNatAux n fun i => w i.succ) / 2 = toNatAux n fun i => w i.succ := by omega
    rw [e, testBit_toNatAux n]
    by_cases h : i < n
    · rw [dif_pos h, dif_pos (Nat.succ_lt_succ h)]
      rfl
    · rw [dif_neg h, dif_neg (fun h' => h (Nat.lt_of_succ_lt_succ h'))]

theorem toNat_lt (w : Word32) : toNat w < 2 ^ 32 := toNatAux_lt 32 w

theorem testBit_toNat (w : Word32) (i : Nat) (hi : i < 32) :
    (toNat w).testBit i = GF2.toBool (w ⟨i, hi⟩) := by
  rw [toNat, testBit_toNatAux, dif_pos hi]

theorem testBit_toNat_of_ge (w : Word32) (i : Nat) (hi : 32 ≤ i) : (toNat w).testBit i = false := by
  rw [toNat, testBit_toNatAux, dif_neg (by omega)]

/-- Bit `i` of a word read as a number, for any `i`. -/
theorem testBit_toNat' (w : Word32) (i : Nat) :
    (toNat w).testBit i = if h : i < 32 then GF2.toBool (w ⟨i, h⟩) else false :=
  testBit_toNatAux 32 w i

@[simp] theorem ofNat_apply (n : Nat) (i : Fin 32) : ofNat n i = GF2.ofBool (n.testBit i) := rfl

theorem toNat_ofNat (n : Nat) : toNat (ofNat n) = n % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_toNat', Nat.testBit_mod_two_pow]
  by_cases h : i < 32
  · simp [h]
  · simp [h]

theorem ofNat_toNat (w : Word32) : ofNat (toNat w) = w := by
  funext i
  rw [ofNat_apply, testBit_toNat w i i.isLt, GF2.ofBool_toBool]

theorem ext_toNat {x y : Word32} (h : toNat x = toNat y) : x = y := by
  rw [← ofNat_toNat x, ← ofNat_toNat y, h]

/-- Two numbers are equal when their bits below `32` agree and both are below `2^32`. -/
theorem eq_of_testBit_lt {a b : Nat} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32)
    (h : ∀ i, i < 32 → a.testBit i = b.testBit i) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · exact h i hi
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))]

theorem toNat_xor (x y : Word32) : toNat (fun i => x i + y i) = toNat x ^^^ toNat y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_toNat', testBit_toNat', testBit_toNat']
  by_cases h : i < 32
  · simp [h, GF2.toBool_add]
  · simp [h]

theorem toNat_and (x y : Word32) : toNat (fun i => x i * y i) = toNat x &&& toNat y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, testBit_toNat', testBit_toNat', testBit_toNat']
  by_cases h : i < 32
  · simp [h, GF2.toBool_mul]
  · simp [h]

theorem testBit_mask (i : Nat) : (0xffffffff : Nat).testBit i = decide (i < 32) := by
  have : (0xffffffff : Nat) = 2 ^ 32 - 1 := by norm_num
  rw [this, Nat.testBit_two_pow_sub_one]

theorem toNat_ch (x y z : Word32) : toNat (ch x y z) = Specs.SHA256.Ch (toNat x) (toNat y) (toNat z) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Specs.SHA256.Ch, Specs.SHA256.not32, Nat.testBit_xor, Nat.testBit_and, testBit_mask, ch,
    testBit_toNat']
  by_cases h : i < 32
  · simp only [h, dite_true, decide_true, GF2.toBool_add, GF2.toBool_mul]
    generalize GF2.toBool (x ⟨i, h⟩) = a
    generalize GF2.toBool (y ⟨i, h⟩) = b
    generalize GF2.toBool (z ⟨i, h⟩) = c
    cases a <;> cases b <;> cases c <;> rfl
  · simp [h]

theorem toNat_maj (x y z : Word32) : toNat (maj x y z) = Specs.SHA256.Maj (toNat x) (toNat y) (toNat z) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Specs.SHA256.Maj, Nat.testBit_xor, Nat.testBit_and, maj, testBit_toNat']
  by_cases h : i < 32
  · simp only [h, dite_true, GF2.toBool_add, GF2.toBool_mul]
  · simp [h]

theorem rotRight32_lt (X n : Nat) (hX : X < 2 ^ 32) : rotRight32 X n < 2 ^ 32 := by
  simp only [rotRight32]
  have hoff : n % 32 < 32 := Nat.mod_lt _ (by decide)
  have hlow : X % 2 ^ (n % 32) < 2 ^ (n % 32) := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hhigh : X / 2 ^ (n % 32) < 2 ^ (32 - n % 32) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rwa [show 32 - n % 32 + n % 32 = 32 by omega]
  have e : 2 ^ 32 = 2 ^ (n % 32) * 2 ^ (32 - n % 32) := by
    rw [← Nat.pow_add, show n % 32 + (32 - n % 32) = 32 by omega]
  have hl : X % 2 ^ (n % 32) + 1 ≤ 2 ^ (n % 32) := hlow
  calc X % 2 ^ (n % 32) * 2 ^ (32 - n % 32) + X / 2 ^ (n % 32)
      < X % 2 ^ (n % 32) * 2 ^ (32 - n % 32) + 2 ^ (32 - n % 32) := by omega
    _ = (X % 2 ^ (n % 32) + 1) * 2 ^ (32 - n % 32) := by ring
    _ ≤ 2 ^ (n % 32) * 2 ^ (32 - n % 32) := Nat.mul_le_mul_right _ hl
    _ = 2 ^ 32 := e.symm

theorem testBit_rotRight32 (X n i : Nat) (hX : X < 2 ^ 32) (hi : i < 32) :
    (rotRight32 X n).testBit i = X.testBit ((i + n) % 32) := by
  simp only [rotRight32]
  have hoff : n % 32 < 32 := Nat.mod_lt _ (by decide)
  have hhigh : X / 2 ^ (n % 32) < 2 ^ (32 - n % 32) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    rwa [show 32 - n % 32 + n % 32 = 32 by omega]
  rw [Nat.mul_comm, Nat.testBit_two_pow_mul_add _ hhigh]
  have hin : (i + n) % 32 = (i + n % 32) % 32 := by omega
  rw [hin]
  by_cases h : i < 32 - n % 32
  · rw [if_pos h, Nat.testBit_div_two_pow, show (i + n % 32) % 32 = i + n % 32 by omega]
  · rw [if_neg h, Nat.testBit_mod_two_pow, show (i + n % 32) % 32 = i - (32 - n % 32) by omega]
    simp [show i - (32 - n % 32) < n % 32 by omega]

theorem toNat_rotr (x : Word32) (n : Nat) :
    toNat (fun i => x ⟨(i.val + n) % 32, Nat.mod_lt _ (by decide)⟩) = rotRight32 (toNat x) n := by
  apply eq_of_testBit_lt (toNat_lt _) (rotRight32_lt _ _ (toNat_lt x))
  intro i hi
  rw [testBit_rotRight32 _ _ _ (toNat_lt x) hi, testBit_toNat _ i hi, testBit_toNat _ _ (Nat.mod_lt _ (by decide))]

theorem toNat_shr (x : Word32) (n : Nat) :
    toNat (fun i => if h : i.val + n < 32 then x ⟨i.val + n, h⟩ else 0) = toNat x / 2 ^ n := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, testBit_toNat', testBit_toNat']
  by_cases h : i < 32
  · rw [dif_pos h]
    by_cases h2 : i + n < 32 <;> simp [h2]
  · have h2 : ¬ (i + n < 32) := by omega
    simp [h, h2]

theorem toNat_add (x y : Word32) : toNat (add x y) = add32 (toNat x) (toNat y) := by
  simp only [add, toNat_ofNat, add32, Nat.mod_mod]

/-- A word as a weighted sum of its bits. -/
theorem toNatAux_eq_sum : ∀ (n : Nat) (w : Fin n → GF2), toNatAux n w = ∑ i : Fin n, (w i).val * 2 ^ i.val
  | 0, _ => by simp [toNatAux]
  | n + 1, w => by
    rw [toNatAux, toNatAux_eq_sum n, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring

theorem toNat_eq_sum (w : Word32) : toNat w = ∑ i : Fin 32, (w i).val * 2 ^ i.val := toNatAux_eq_sum 32 w

theorem fullAdder_val (a b c : GF2) : (a + b + c).val + 2 * (a * b + a * c + b * c).val = a.val + b.val + c.val := by
  revert a b c; decide

/-- Carry-save compression preserves the sum modulo `2^32`. -/
theorem csa_sum (x y z : Word32) :
    (toNat (csaSum x y z) + toNat (csaCarry x y z)) % 2 ^ 32 = (toNat x + toNat y + toNat z) % 2 ^ 32 := by
  have hS : toNat (csaSum x y z) + 2 * ∑ i : Fin 32, (maj x y z i).val * 2 ^ i.val
      = toNat x + toNat y + toNat z := by
    simp only [toNat_eq_sum, csaSum, maj, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := fullAdder_val (x i) (y i) (z i)
    calc (x i + y i + z i).val * 2 ^ i.val + 2 * ((x i * y i + x i * z i + y i * z i).val * 2 ^ i.val)
        = ((x i + y i + z i).val + 2 * (x i * y i + x i * z i + y i * z i).val) * 2 ^ i.val := by ring
      _ = ((x i).val + (y i).val + (z i).val) * 2 ^ i.val := by rw [this]
      _ = _ := by ring
  have hC : toNat (csaCarry x y z) + (maj x y z ⟨31, by decide⟩).val * 2 ^ 32
      = 2 * ∑ i : Fin 32, (maj x y z i).val * 2 ^ i.val := by
    rw [toNat_eq_sum, Fin.sum_univ_succ, Fin.sum_univ_castSucc (n := 31), mul_add, Finset.mul_sum]
    simp only [csaCarry, Fin.val_zero, Fin.val_succ, Fin.val_castSucc, Fin.val_last]
    simp only [dite_true, ZMod.val_zero, zero_mul, zero_add]
    have e : ∀ i : Fin 31, (if h : i.val + 1 = 0 then (0 : GF2) else maj x y z ⟨i.val + 1 - 1, by omega⟩)
        = maj x y z ⟨i.val, by omega⟩ := fun i => by
      rw [dif_neg (by omega)]
      congr 1
    simp only [e]
    have e2 : ∀ i : Fin 31, (maj x y z ⟨i.val, by omega⟩).val * 2 ^ (i.val + 1)
        = 2 * ((maj x y z (Fin.castSucc i)).val * 2 ^ i.val) := fun i => by
      rw [Fin.castSucc]; simp only [Fin.castAdd, Fin.castLE]; ring
    simp only [e2]
    rw [show (⟨31, by decide⟩ : Fin 32) = Fin.last 31 from rfl]
    ring
  have key : toNat (csaSum x y z) + toNat (csaCarry x y z) + (maj x y z ⟨31, by decide⟩).val * 2 ^ 32
      = toNat x + toNat y + toNat z := by omega
  rw [← key, Nat.add_mul_mod_self_right]

theorem toNat_sumList (ws : List Word32) : toNat (sumList ws) = (ws.map toNat).sum % 2 ^ 32 := by
  simp only [sumList, toNat_ofNat, Nat.mod_mod]

end Word32

end WeftChals
