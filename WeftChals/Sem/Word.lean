import WeftChals.Sem.Adder
import Mathlib.Data.List.InsertIdx

/-!
# The word gadgets compute the word operations
-/
namespace WeftChals
open Weft

theorem Word.ch_val (x y z : Word GF2) : (Id.run (Word.ch (m := Id) x y z)).val = Word32.ch x.val y.val z.val := by
  funext i
  show Bit.val (Id.run (vecM 32 fun i => Bit.ch3 (x i) (y i) (z i)) i) = _
  rw [vecM_Id]
  exact Bit.val_ch3 _ _ _

theorem Word.maj_val (x y z : Word GF2) : (Id.run (Word.maj (m := Id) x y z)).val = Word32.maj x.val y.val z.val := by
  funext i
  show Bit.val (Id.run (vecM 32 fun i => Bit.maj3 (x i) (y i) (z i)) i) = _
  rw [vecM_Id]
  exact Bit.val_maj3 _ _ _

theorem Word.csa3_val (x y z : Word GF2) :
    (Id.run (Word.csa3 (m := Id) x y z)).1.val = Word32.csaSum x.val y.val z.val ∧
    (Id.run (Word.csa3 (m := Id) x y z)).2.val = Word32.csaCarry x.val y.val z.val := by
  refine ⟨?_, ?_⟩
  · funext i
    show Bit.val (Id.run (vecM 32 fun i => do
      let t ← Bit.xor (m := Id) (x i) (y i)
      Bit.xor t (z i)) i) = _
    rw [vecM_Id]
    show Bit.val (Id.run (Bit.xor (m := Id) (Id.run (Bit.xor (m := Id) (x i) (y i))) (z i))) = _
    rw [Bit.val_xor, Bit.val_xor]
    rfl
  · funext i
    show Bit.val (Id.run (vecM 32 fun i =>
      if h : i.val = 0 then pure (Bit.const false)
      else Bit.maj3 (m := Id) (x ⟨i.val - 1, by omega⟩) (y ⟨i.val - 1, by omega⟩) (z ⟨i.val - 1, by omega⟩)) i) = _
    rw [vecM_Id]
    simp only [Word32.csaCarry]
    split
    · rfl
    · rw [Bit.val_maj3]
      rfl

/-! ## Multi-operand sums -/

namespace Sum32

/-- The sum of a list of words, modulo `2^32`. -/
def S (ws : List (Word GF2)) : Nat := ((ws.map Word.val).map Word32.toNat).sum % 2 ^ 32

theorem S_cons (w : Word GF2) (ws : List (Word GF2)) : S (w :: ws) = (Word32.toNat w.val + S ws) % 2 ^ 32 := by
  simp [S, Nat.add_mod]

theorem S_append_two (ws : List (Word GF2)) (s c : Word GF2) :
    S (ws ++ [s, c]) = (S ws + Word32.toNat s.val + Word32.toNat c.val) % 2 ^ 32 := by
  simp [S, Nat.add_mod, Nat.add_assoc]

theorem sum_eraseIdx (l : List Nat) (i : Nat) (h : i < l.length) : (l.eraseIdx i).sum + l[i] = l.sum := by
  rw [List.eraseIdx_eq_take_drop_succ, List.sum_append]
  conv_rhs => rw [← List.take_append_drop i l, List.sum_append, List.drop_eq_getElem_cons h, List.sum_cons]
  omega

/-- Erasing three distinct positions (largest first) takes the three elements out of the sum. -/
theorem sum_erase3 (l : List Nat) (hi mid lo : Nat) (h1 : lo < mid) (h2 : mid < hi) (h3 : hi < l.length) :
    (((l.eraseIdx hi).eraseIdx mid).eraseIdx lo).sum + l[hi] + l[mid] + l[lo] = l.sum := by
  have hl1 : mid < (l.eraseIdx hi).length := by rw [List.length_eraseIdx_of_lt h3]; omega
  have hl2 : lo < ((l.eraseIdx hi).eraseIdx mid).length := by rw [List.length_eraseIdx_of_lt hl1]; omega
  have e1 := sum_eraseIdx _ lo hl2
  have e2 := sum_eraseIdx _ mid hl1
  have e3 := sum_eraseIdx l hi h3
  rw [List.getElem_eraseIdx_of_lt hl2 h1, List.getElem_eraseIdx_of_lt (by omega) (by omega)] at e1
  rw [List.getElem_eraseIdx_of_lt hl1 h2] at e2
  omega

theorem sum_erase3' (l : List Nat) (hi mid lo : Nat) (h1 : lo < mid) (h2 : mid < hi) (h3 : hi < l.length) :
    (((l.eraseIdx hi).eraseIdx mid).eraseIdx lo).sum + l.getD hi 0 + l.getD mid 0 + l.getD lo 0 = l.sum := by
  rw [List.getD_eq_getElem _ _ h3, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
  exact sum_erase3 l hi mid lo h1 h2 h3

/-- The three positions, in whichever order, are `i`, `j`, `k`. -/
theorem getD_perm3 (l : List Nat) (i j k : Nat) :
    l.getD (max i (max j k)) 0 + l.getD (i + j + k - max i (max j k) - min i (min j k)) 0 + l.getD (min i (min j k)) 0
      = l.getD i 0 + l.getD j 0 + l.getD k 0 := by
  have h6 : (max i (max j k) = i ∧ min i (min j k) = j) ∨ (max i (max j k) = i ∧ min i (min j k) = k) ∨
      (max i (max j k) = j ∧ min i (min j k) = i) ∨ (max i (max j k) = j ∧ min i (min j k) = k) ∨
      (max i (max j k) = k ∧ min i (min j k) = i) ∨ (max i (max j k) = k ∧ min i (min j k) = j) := by omega
  rcases h6 with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rw [a1, a2]
  · rw [show i + j + k - i - j = k by omega]; try ring
  · rw [show i + j + k - i - k = j by omega]; try ring
  · rw [show i + j + k - j - i = k by omega]; try ring
  · rw [show i + j + k - j - k = i by omega]; try ring
  · rw [show i + j + k - k - i = j by omega]; try ring
  · rw [show i + j + k - k - j = i by omega]; try ring

theorem step_S (ws : List (Word GF2)) (code : Nat) : S (Id.run (Sum32.step (m := Id) ws code)) = S ws := by
  simp only [Sum32.step]
  split
  · rename_i hc
    obtain ⟨hi, hj, hk, hij, hik, hjk⟩ := hc
    generalize hI : (SumPlan.decodeStep code).1 = i at *
    generalize hJ : (SumPlan.decodeStep code).2.1 = j at *
    generalize hK : (SumPlan.decodeStep code).2.2 = k at *
    show S (_ ++ [(Id.run (Word.csa3 (m := Id) _ _ _)).1, (Id.run (Word.csa3 (m := Id) _ _ _)).2]) = S ws
    rw [S_append_two, (Word.csa3_val _ _ _).1, (Word.csa3_val _ _ _).2, Nat.add_assoc, Nat.add_mod,
      Word32.csa_sum, ← Nat.add_mod]
    have hx : ∀ a, a < ws.length →
        Word32.toNat (ws.getD a (Word.const 0)).val = ((ws.map Word.val).map Word32.toNat).getD a 0 := by
      intro a ha
      rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ (by simpa)]
      simp
    rw [hx i hi, hx j hj, hx k hk]
    have hS : S (((ws.eraseIdx (max i (max j k))).eraseIdx (i + j + k - max i (max j k) - min i (min j k))).eraseIdx
        (min i (min j k))) = ((((ws.map Word.val).map Word32.toNat).eraseIdx (max i (max j k))).eraseIdx
        (i + j + k - max i (max j k) - min i (min j k)) |>.eraseIdx (min i (min j k))).sum % 2 ^ 32 := by
      simp only [S, List.eraseIdx_map]
    rw [hS, Nat.mod_add_mod, ← getD_perm3 _ i j k, ← Nat.add_assoc, ← Nat.add_assoc,
      sum_erase3' _ _ _ _ (by omega) (by omega) (by simp; omega)]
    rfl
  · rfl

theorem foldl_step_S (ws : List (Word GF2)) : ∀ (cs : List Nat),
    S (List.foldl (fun ws c => Id.run (Sum32.step (m := Id) ws c)) ws cs) = S ws
  | [] => rfl
  | c :: cs => by
    rw [List.foldl_cons]
    have := foldl_step_S (Id.run (Sum32.step (m := Id) ws c)) cs
    rw [this, step_S]

theorem finish_S (net : Net) : ∀ (fuel : Nat) (ws : List (Word GF2)), ws.length ≤ fuel →
    Word32.toNat (Id.run (Sum32.finish (m := Id) net fuel ws)).val = S ws
  | _, [], _ => by
    simp only [Sum32.finish, S, List.map_nil, List.sum_nil, Nat.zero_mod]
    show Word32.toNat (Word.const 0 : Word GF2).val = 0
    have : (Word.const 0 : Word GF2).val = Word32.ofNat 0 := rfl
    rw [this, Word32.toNat_ofNat]
    exact Nat.zero_mod _
  | _, [x], _ => by
    simp only [Sum32.finish, S, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact (Nat.mod_eq_of_lt (Word32.toNat_lt _)).symm
  | _, [x, y], _ => by
    simp only [Sum32.finish, S, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Adder.add_val, Word32.toNat_add, add32]
  | 0, x :: y :: z :: rest, h => by simp at h
  | fuel + 1, x :: y :: z :: rest, h => by
    simp only [Sum32.finish]
    show Word32.toNat (Id.run (Sum32.finish (m := Id) net fuel
      (rest ++ [(Id.run (Word.csa3 (m := Id) x y z)).1, (Id.run (Word.csa3 (m := Id) x y z)).2]))).val = _
    rw [finish_S net fuel _ (by simp at h ⊢; omega), S_append_two, (Word.csa3_val _ _ _).1, (Word.csa3_val _ _ _).2,
      Nat.add_assoc, Nat.add_mod, Word32.csa_sum, ← Nat.add_mod, S_cons, S_cons, S_cons]
    omega

theorem sum_val (plan : SumPlan) (ws : List (Word GF2)) :
    (Id.run (Sum32.sum (m := Id) plan ws)).val = Word32.sumList (ws.map Word.val) := by
  apply Word32.ext_toNat
  rw [Word32.toNat_sumList]
  show Word32.toNat (Id.run (Sum32.finish (m := Id) plan.net (Id.run (foldM (Sum32.step (m := Id)) ws plan.csa)).length
    (Id.run (foldM (Sum32.step (m := Id)) ws plan.csa)))).val = _
  rw [finish_S _ _ _ (le_refl _), foldM_Id, foldl_step_S]
  rfl

end Sum32

theorem chReal_val (x y z : Wd GF2) : Id.run (chReal (m := Id) x y z) = Word32.ch x y z := by
  show Id.run (Word.materialize (m := Id) (Id.run (Word.ch (m := Id) (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)))) = _
  rw [Word.materialize_Id, Word.ch_val]
  rfl

theorem majReal_val (x y z : Wd GF2) : Id.run (majReal (m := Id) x y z) = Word32.maj x y z := by
  show Id.run (Word.materialize (m := Id) (Id.run (Word.maj (m := Id) (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)))) = _
  rw [Word.materialize_Id, Word.maj_val]
  rfl

theorem csaReal_val (x y z : Wd GF2) :
    Id.run (csaReal (m := Id) x y z) = (Word32.csaSum x y z, Word32.csaCarry x y z) := by
  show (Id.run (Word.materialize (m := Id) (Id.run (Word.csa3 (m := Id) (Word.ofShares x) (Word.ofShares y) (Word.ofShares z))).1),
    Id.run (Word.materialize (m := Id) (Id.run (Word.csa3 (m := Id) (Word.ofShares x) (Word.ofShares y) (Word.ofShares z))).2)) = _
  rw [Word.materialize_Id, Word.materialize_Id, (Word.csa3_val _ _ _).1, (Word.csa3_val _ _ _).2]
  rfl

theorem addReal_val (net : Net) (x y : Wd GF2) : Id.run (addReal (m := Id) net x y) = Word32.add x y := by
  show Id.run (Word.materialize (m := Id) (Id.run (Adder.add (m := Id) net (Word.ofShares x) (Word.ofShares y)))) = _
  rw [Word.materialize_Id, Adder.add_val]
  rfl

theorem sumReal_val (plan : SumPlan) (ws : List (Wd GF2)) :
    Id.run (sumReal (m := Id) plan ws) = Word32.sumList ws := by
  show Id.run (Word.materialize (m := Id) (Id.run (Sum32.sum (m := Id) plan (ws.map Word.ofShares)))) = _
  rw [Word.materialize_Id, Sum32.sum_val, List.map_map]
  simp [Function.comp_def]

end WeftChals
