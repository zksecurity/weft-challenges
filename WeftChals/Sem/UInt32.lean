import WeftChals.Sem.Bits
import Wychelean.Hashes.SHA256

/-! # Shared-bit words and Wychelean's fixed-width words -/
namespace WeftChals.Word32
open Weft

@[simp] theorem toNat_toUInt32 (w : Word32) : (toUInt32 w).toNat = toNat w := by
  exact Nat.mod_eq_of_lt (toNat_lt w)

@[simp] theorem toUInt32_ofNat (n : Nat) : toUInt32 (ofNat n) = n.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [toNat_ofNat]

theorem ext_toUInt32 {x y : Word32} (h : toUInt32 x = toUInt32 y) : x = y := by
  apply ext_toNat
  simpa using congrArg UInt32.toNat h

@[simp] theorem toUInt32_xor (x y : Word32) :
    toUInt32 (fun i => x i + y i) = toUInt32 x ^^^ toUInt32 y := by
  apply UInt32.toNat_inj.mp
  simp [toNat_xor]

@[simp] theorem toUInt32_ch (x y z : Word32) :
    toUInt32 (ch x y z) = Wychelean.Hashes.SHA256.Ch (toUInt32 x) (toUInt32 y) (toUInt32 z) := by
  apply UInt32.toNat_inj.mp
  simp only [toNat_toUInt32, toNat_ch, Wychelean.Hashes.SHA256.Ch,
    UInt32.toNat_xor, UInt32.toNat_and]
  have hn : (~~~(toUInt32 x)).toNat = toNat x ^^^ 0xffffffff := by
    change (~~~(toUInt32 x).toBitVec).toNat = _
    rw [BitVec.not_def, BitVec.toNat_xor]
    simp [Nat.xor_comm]
  rw [hn]

@[simp] theorem toUInt32_maj (x y z : Word32) :
    toUInt32 (maj x y z) = Wychelean.Hashes.SHA256.Maj (toUInt32 x) (toUInt32 y) (toUInt32 z) := by
  apply UInt32.toNat_inj.mp
  simp [toNat_maj, Wychelean.Hashes.SHA256.Maj]

@[simp] theorem toUInt32_rotr (x : Word32) (n : Nat) :
    toUInt32 (fun i => x ⟨(i.val + n) % 32, Nat.mod_lt _ (by decide)⟩) = Wychelean.rotr n (toUInt32 x) := by
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getElem_eq
  intro i hi
  change (toUInt32 (fun i => x ⟨(i.val + n) % 32, _⟩)).toBitVec[i] =
    ((toUInt32 x).toBitVec.rotateRight n)[i]
  rw [BitVec.getElem_rotateRight]
  simp only [BitVec.getElem_eq_testBit_toNat, UInt32.toNat_toBitVec, toNat_toUInt32]
  split <;> rw [testBit_toNat _ _ hi, testBit_toNat _ _ (by omega)] <;> congr 2 <;> apply Fin.ext <;> dsimp only <;> omega

@[simp] theorem toUInt32_shr (x : Word32) (n : Nat) (hn : n < 32) :
    toUInt32 (fun i => if h : i.val + n < 32 then x ⟨i.val + n, h⟩ else 0) = toUInt32 x >>> n.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp only [toNat_toUInt32, toNat_shr, UInt32.toNat_shiftRight, Nat.toUInt32_eq,
    UInt32.toNat_ofNat', Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt hn]

@[simp] theorem toUInt32_add (x y : Word32) : toUInt32 (add x y) = toUInt32 x + toUInt32 y := by
  apply UInt32.toNat_inj.mp
  simp [toNat_add, add32]

@[simp] theorem toUInt32_sumList_nil : toUInt32 (sumList []) = 0 := by
  apply UInt32.toNat_inj.mp
  simp [toNat_sumList]

@[simp] theorem toUInt32_sumList_cons (x : Word32) (xs : List Word32) :
    toUInt32 (sumList (x :: xs)) = toUInt32 x + toUInt32 (sumList xs) := by
  apply UInt32.toNat_inj.mp
  simp only [toNat_toUInt32, toNat_sumList, List.map_cons, List.sum_cons, UInt32.toNat_add]
  omega

theorem toUInt32_csa (x y z : Word32) :
    toUInt32 (csaSum x y z) + toUInt32 (csaCarry x y z) = toUInt32 x + toUInt32 y + toUInt32 z := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, toNat_toUInt32]
  have := csa_sum x y z
  omega

end WeftChals.Word32
