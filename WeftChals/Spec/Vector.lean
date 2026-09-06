import Mathlib.Data.PNat.Defs

/-!
# Vector helpers used by the SHA-256 specification

`Clean.Utils.Vector` provides `mapFinRange` and `toChunks`; here they are
defined directly by `Vector.ofFn`, which is what the proofs use.
-/
namespace Vector

/-- The vector whose `i`th entry is `create i`. -/
def mapFinRange {α : Type} (n : ℕ) (create : Fin n → α) : Vector α n := Vector.ofFn create

@[simp] theorem getElem_mapFinRange {α : Type} {n : ℕ} (create : Fin n → α) (i : ℕ) (hi : i < n) :
    (mapFinRange n create)[i] = create ⟨i, hi⟩ := by
  simp [mapFinRange]

theorem chunk_index_lt {n m i j : ℕ} (hi : i < n) (hj : j < m) : i * m + j < n * m := by
  have h : (i + 1) * m ≤ n * m := Nat.mul_le_mul_right m hi
  rw [Nat.add_mul, Nat.one_mul] at h
  omega

/-- Split a vector of length `n * m` into `n` chunks of length `m`. -/
def toChunks {n : ℕ} (m : ℕ+) {α : Type} (v : Vector α (n * m)) : Vector (Vector α m) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => v[i.val * m + j.val]'(chunk_index_lt i.isLt j.isLt)

@[simp] theorem getElem_toChunks {n : ℕ} (m : ℕ+) {α : Type} (v : Vector α (n * m))
    (i j : ℕ) (hi : i < n) (hj : j < m) :
    (toChunks m v)[i][j] = v[i * m + j]'(chunk_index_lt hi hj) := by
  simp [toChunks]

end Vector

namespace Vector
/-- The length of a vector, as `Clean.Utils.Vector` names it. -/
def len {α : Type} {n : ℕ} (_ : Vector α n) : ℕ := n
end Vector
