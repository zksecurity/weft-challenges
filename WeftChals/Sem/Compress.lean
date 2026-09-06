import WeftChals.Circuit.Compress
import WeftChals.Functionality.Compress
import WeftChals.Sem.Bits
import WeftChals.Sem.Value

/-!
# The compression program computes `compressBlock`

At the ideal word operations, the program over `Hyb` is the specification:
the schedule fills the message schedule, each round is `sha256Round`, and
the feed-forward is the final addition.
-/
namespace WeftChals
open Weft

@[simp] theorem Id.run_bind'' {α β : Type} (x : Id α) (f : α → Id β) : Id.run (x >>= f) = Id.run (f (Id.run x)) := rfl
@[simp] theorem Id.run_pure'' {α : Type} (a : α) : Id.run (pure a : Id α) = a := rfl

namespace Compress

/-! ## Words -/

theorem xorW_Id (x y : Word32) : Id.run (xorW (m := Id) x y) = fun i => x i + y i := by
  funext i; simp [xorW, vecM_Id]; rfl

theorem xor3W_Id (x y z : Word32) : Id.run (xor3W (m := Id) x y z) = fun i => x i + y i + z i := by
  simp only [xor3W, Id.run_bind'', xorW_Id]

theorem shrW_Id (x : Word32) (n : Nat) :
    Id.run (shrW (m := Id) x n) = fun i => if h : i.val + n < 32 then x ⟨i.val + n, h⟩ else 0 := by
  funext i
  simp only [shrW, vecM_Id]
  split <;> rfl

theorem constW_Id (n : Nat) : Id.run (constW (m := Id) n) = Word32.ofNat n := by
  funext i; simp [constW, vecM_Id]; rfl

theorem toNat_sigma0 (x : Word32) : Word32.toNat (Id.run (sigma0 (m := Id) x)) = Specs.SHA256.lowerSigma0 (Word32.toNat x) := by
  simp only [sigma0, Id.run_bind'', shrW_Id, xor3W_Id, rotrW, Specs.SHA256.lowerSigma0]
  rw [Word32.toNat_xor (fun i => x _ + x _) _, Word32.toNat_xor, Word32.toNat_rotr, Word32.toNat_rotr, Word32.toNat_shr]

theorem toNat_sigma1 (x : Word32) : Word32.toNat (Id.run (sigma1 (m := Id) x)) = Specs.SHA256.lowerSigma1 (Word32.toNat x) := by
  simp only [sigma1, Id.run_bind'', shrW_Id, xor3W_Id, rotrW, Specs.SHA256.lowerSigma1]
  rw [Word32.toNat_xor (fun i => x _ + x _) _, Word32.toNat_xor, Word32.toNat_rotr, Word32.toNat_rotr, Word32.toNat_shr]

theorem toNat_bigSigma0 (x : Word32) :
    Word32.toNat (Id.run (bigSigma0 (m := Id) x)) = Specs.SHA256.upperSigma0 (Word32.toNat x) := by
  simp only [bigSigma0, xor3W_Id, rotrW, Specs.SHA256.upperSigma0]
  rw [Word32.toNat_xor (fun i => x _ + x _) _, Word32.toNat_xor, Word32.toNat_rotr, Word32.toNat_rotr, Word32.toNat_rotr]

theorem toNat_bigSigma1 (x : Word32) :
    Word32.toNat (Id.run (bigSigma1 (m := Id) x)) = Specs.SHA256.upperSigma1 (Word32.toNat x) := by
  simp only [bigSigma1, xor3W_Id, rotrW, Specs.SHA256.upperSigma1]
  rw [Word32.toNat_xor (fun i => x _ + x _) _, Word32.toNat_xor, Word32.toNat_rotr, Word32.toNat_rotr, Word32.toNat_rotr]

theorem ch_Id (x y z : Word32) : Id.run (WordM.ch (m := Id) x y z) = Word32.ch x y z := rfl
theorem maj_Id (x y z : Word32) : Id.run (WordM.maj (m := Id) x y z) = Word32.maj x y z := rfl
theorem sum_Id (p : SumPlan) (ws : List Word32) : Id.run (WordM.sum (m := Id) p ws) = Word32.sumList ws := rfl
theorem add_Id (net : Net) (x y : Word32) : Id.run (WordM.add (m := Id) net x y) = Word32.add x y := rfl
theorem csa_Id (x y z : Word32) :
    Id.run (WordM.csa (m := Id) x y z) = (Word32.csaSum x y z, Word32.csaCarry x y z) := rfl

/-! ## Iteration -/

/-- Apply `f 0`, then `f 1`, …, then `f (t - 1)`. -/
def iter {β : Type} (f : Nat → β → β) : Nat → β → β
  | 0, s => s
  | t + 1, s => f t (iter f t s)

theorem iter_congr {β : Type} {f g : Nat → β → β} : ∀ (t : Nat) (s : β), (∀ i, i < t → ∀ st, f i st = g i st) →
    iter f t s = iter g t s
  | 0, _, _ => rfl
  | t + 1, s, h => by
    simp only [iter, iter_congr t s fun i hi st => h i (by omega) st, h t (by omega)]

theorem foldl_eq_iter {α β : Type} (g : β → α → β) (d : α) : ∀ (l : List α) (s : β),
    List.foldl g s l = iter (fun i st => g st (l.getD i d)) l.length s
  | [], _ => rfl
  | a :: l, s => by
    rw [List.foldl_cons, foldl_eq_iter g d l (g s a), List.length_cons]
    have shift : ∀ (n : Nat) (s : β), iter (fun i st => g st ((a :: l).getD i d)) (n + 1) s
        = iter (fun i st => g st (l.getD i d)) n (g s a) := by
      intro n
      induction n with
      | zero => intro s; rfl
      | succ n ih => intro s; rw [iter, ih]; rfl
    exact (shift l.length s).symm

theorem finFoldl_eq_iter {β : Type} : ∀ (t : Nat) (F : β → Fin t → β) (x : β),
    Fin.foldl t F x = iter (fun i st => if h : i < t then F st ⟨i, h⟩ else st) t x
  | 0, _, x => by rw [Fin.foldl_zero]; rfl
  | t + 1, F, x => by
    rw [Fin.foldl_succ_last, finFoldl_eq_iter t]
    simp only [iter, Nat.lt_succ_self, dite_true]
    congr 1
    apply iter_congr
    intro i hi st
    simp only [hi, dite_true, show i < t + 1 by omega]
    rfl

/-! ## The schedule -/

/-- One schedule step of the specification, on a full vector. -/
def specStep (w : Vector ℕ 64) (j : Nat) (hj : j < 64) : Vector ℕ 64 :=
  w.set j (add32 (add32 (Specs.SHA256.lowerSigma1 w[j - 2]) w[j - 7])
    (add32 (Specs.SHA256.lowerSigma0 w[j - 15]) w[j - 16]))

theorem specStep_get (w : Vector ℕ 64) (j : Nat) (hj : j < 64) (i : Nat) (hi : i < 64) :
    (specStep w j hj)[i] = if i = j then add32 (add32 (Specs.SHA256.lowerSigma1 w[j - 2]) w[j - 7])
      (add32 (Specs.SHA256.lowerSigma0 w[j - 15]) w[j - 16]) else w[i] := by
  simp only [specStep]
  split
  · subst_vars; simp
  · rw [Vector.getElem_set_ne _ _ (by omega)]

/-- The schedule after `t` steps. -/
def sched (blk : Vector ℕ 16) : Nat → Vector ℕ 64
  | 0 => Vector.mapFinRange 64 fun i => if h : i.val < 16 then blk.get ⟨i.val, h⟩ else 0
  | t + 1 => if h : t + 16 < 64 then specStep (sched blk t) (t + 16) h else sched blk t

theorem messageSchedule_eq (blk : Vector ℕ 16) : Specs.SHA256.messageSchedule blk = sched blk 48 := by
  simp only [Specs.SHA256.messageSchedule]
  rw [finFoldl_eq_iter]
  have : ∀ t, t ≤ 48 → iter (fun i st => if h : i < 48 then
      (let j := i + 16
       let wj := add32 (add32 (Specs.SHA256.lowerSigma1 st[j - 2]) st[j - 7])
         (add32 (Specs.SHA256.lowerSigma0 st[j - 15]) st[j - 16])
       st.set j wj) else st) t
      (Vector.mapFinRange 64 fun i => if h : i.val < 16 then blk.get ⟨i.val, h⟩ else 0) = sched blk t := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      simp only [iter, ih (by omega), sched, show t < 48 by omega, dite_true, show t + 16 < 64 by omega]
      rfl
  exact this 48 (le_refl _)

theorem sched_get_lt (blk : Vector ℕ 16) : ∀ (t : Nat) (i : Nat) (hi : i < 64), i < 16 + t → t ≤ 48 →
    (sched blk 48)[i] = (sched blk t)[i]
  | 48, _, _, _, _ => rfl
  | t, i, hi, hit, ht => by
    rcases Nat.lt_or_ge t 48 with hlt | hge
    · have := sched_get_lt blk (t + 1) i hi (by omega) (by omega)
      rw [this]
      simp only [sched, show t + 16 < 64 by omega, dite_true, specStep_get, show ¬ i = t + 16 by omega, if_false]
    · have : t = 48 := by omega
      subst this
      rfl
termination_by t => 48 - t

theorem sched_zero (blk : Vector ℕ 16) (i : Nat) (hi : i < 16) : (sched blk 0)[i] = blk[i] := by
  simp [sched, hi]
  try rfl

theorem sched_succ_last (blk : Vector ℕ 16) (t : Nat) (ht : t < 48) :
    (sched blk (t + 1))[16 + t]'(by omega) = add32 (add32 (Specs.SHA256.lowerSigma1 ((sched blk t)[16 + t - 2]'(by omega)))
      ((sched blk t)[16 + t - 7]'(by omega)))
      (add32 (Specs.SHA256.lowerSigma0 ((sched blk t)[16 + t - 15]'(by omega))) ((sched blk t)[16 + t - 16]'(by omega))) := by
  simp only [sched, show t + 16 < 64 by omega, dite_true, specStep_get, show 16 + t = t + 16 by omega, if_true]

/-- The circuit's schedule list agrees with the specification's schedule so far. -/
def SI (blk : Vector ℕ 16) (t : Nat) (W : List Word32) : Prop :=
  W.length = 16 + t ∧ ∀ i (hi : i < 16 + t) (hW : i < W.length) (h64 : i < 64), Word32.toNat W[i] = (sched blk t)[i]

theorem scheduleStep_SI (blk : Vector ℕ 16) (zero : Word32) (t : Nat) (ht : t < 48) (W : List Word32) (p : SumPlan)
    (h : SI blk t W) : SI blk (t + 1) (Id.run (scheduleStep (m := Id) zero W p)) := by
  obtain ⟨hlen, hval⟩ := h
  simp only [scheduleStep, Id.run_bind'', Id.run_pure'']
  have hW : ∀ j (hj : j < 16 + t), W.getD j zero = W[j]'(by omega) := fun j hj =>
    List.getD_eq_getElem _ _ (by omega)
  refine ⟨by rw [List.length_append, hlen]; rfl, fun i hi hW' h64 => ?_⟩
  rcases Nat.lt_or_ge i (16 + t) with hlt | hge
  · rw [List.getElem_append_left (by omega), hval i hlt (by omega) h64]
    simp only [sched, show t + 16 < 64 by omega, dite_true, specStep_get, show ¬ i = t + 16 by omega, if_false]
  · have hi' : i = 16 + t := by omega
    subst hi'
    rw [List.getElem_append_right (by omega), List.getElem_singleton, sched_succ_last blk t ht]
    show Word32.toNat (Word32.sumList _) = _
    rw [Word32.toNat_sumList, hlen]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [hW (16 + t - 2) (by omega), hW (16 + t - 7) (by omega), hW (16 + t - 15) (by omega), hW (16 + t - 16) (by omega),
      toNat_sigma1, toNat_sigma0, hval _ (by omega) (by omega) (by omega), hval _ (by omega) (by omega) (by omega),
      hval _ (by omega) (by omega) (by omega), hval _ (by omega) (by omega) (by omega)]
    simp only [add32, Nat.reducePow]
    omega

theorem schedule_SI (blk : Vector ℕ 16) (zero : Word32) (ps : List SumPlan) (hps : ps.length = 48)
    (W : List Word32) (h : SI blk 0 W) :
    SI blk 48 (Id.run (foldM (scheduleStep (m := Id) zero) W ps)) := by
  rw [foldM_Id]
  have : ∀ (t : Nat) (ps : List SumPlan) (W : List Word32), t + ps.length ≤ 48 → SI blk t W →
      SI blk (t + ps.length) (List.foldl (fun W p => Id.run (scheduleStep (m := Id) zero W p)) W ps) := by
    intro t ps
    induction ps generalizing t with
    | nil => intro W _ h; simpa using h
    | cons p ps ih =>
      intro W hlen h
      rw [List.foldl_cons]
      have := ih (t + 1) _ (by simp at hlen ⊢; omega) (scheduleStep_SI blk zero t (by simp at hlen; omega) W p h)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this
  have := this 0 ps W (by omega) h
  rwa [hps] at this

theorem finList_SI (blk : Vector ℕ 16) (block : Fin 16 → Word32) (hblk : blk = wordsNat block) :
    SI blk 0 (finList 16 block) := by
  rw [finList_eq_ofFn]
  refine ⟨by simp, fun i hi hW h64 => ?_⟩
  rw [List.getElem_ofFn, sched_zero blk i (by omega), hblk]
  simp [wordsNat]

/-! ## The rounds -/

/-- The words of a state, as numbers. -/
def stateNat (st : State GF2) : Vector ℕ 8 :=
  #v[Word32.toNat st.a, Word32.toNat st.b, Word32.toNat st.c, Word32.toNat st.d,
     Word32.toNat st.e, Word32.toNat st.f, Word32.toNat st.g, Word32.toNat st.h]

/-- The entries of a vector literal (with the entries abstract, so that the
kernel never evaluates them). -/
theorem vec8_get {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[0] = a0 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[1] = a1 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[2] = a2 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[3] = a3 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[4] = a4 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[5] = a5 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[6] = a6 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[7] = a7 := by
  simp

/-- The specification's `T1`. -/
def T1 (state : Vector ℕ 8) (k w : ℕ) : ℕ :=
  add32 (add32 (add32 (add32 state[7] (Specs.SHA256.upperSigma1 state[4])) (Specs.SHA256.Ch state[4] state[5] state[6])) k) w
/-- The specification's `T2`. -/
def T2 (state : Vector ℕ 8) : ℕ :=
  add32 (Specs.SHA256.upperSigma0 state[0]) (Specs.SHA256.Maj state[0] state[1] state[2])

theorem sha256Round_lit (state : Vector ℕ 8) (k w : ℕ) :
    Specs.SHA256.sha256Round state k w = #v[add32 (T1 state k w) (T2 state), state[0], state[1], state[2],
      add32 state[3] (T1 state k w), state[4], state[5], state[6]] := rfl

/-- The entries of the specification's round. -/
theorem sha256Round_get (state : Vector ℕ 8) (k w : Nat) :
    (Specs.SHA256.sha256Round state k w)[0] = add32 (T1 state k w) (T2 state) ∧
    (Specs.SHA256.sha256Round state k w)[1] = state[0] ∧ (Specs.SHA256.sha256Round state k w)[2] = state[1] ∧
    (Specs.SHA256.sha256Round state k w)[3] = state[2] ∧
    (Specs.SHA256.sha256Round state k w)[4] = add32 state[3] (T1 state k w) ∧
    (Specs.SHA256.sha256Round state k w)[5] = state[4] ∧ (Specs.SHA256.sha256Round state k w)[6] = state[5] ∧
    (Specs.SHA256.sha256Round state k w)[7] = state[6] := by
  rw [sha256Round_lit]
  exact vec8_get _ _ _ _ _ _ _ _

theorem stateNat_get (st : State GF2) :
    (stateNat st)[0] = Word32.toNat st.a ∧ (stateNat st)[1] = Word32.toNat st.b ∧ (stateNat st)[2] = Word32.toNat st.c ∧
    (stateNat st)[3] = Word32.toNat st.d ∧ (stateNat st)[4] = Word32.toNat st.e ∧ (stateNat st)[5] = Word32.toNat st.f ∧
    (stateNat st)[6] = Word32.toNat st.g ∧ (stateNat st)[7] = Word32.toNat st.h := by
  simp only [stateNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, and_self]

theorem round_spec (st : State GF2) (k : Nat) (w : Word32) (rp : RoundPlan) :
    stateNat (Id.run (round (m := Id) st (k, w, rp))) = Specs.SHA256.sha256Round (stateNat st) k (Word32.toNat w) := by
  simp only [round, Id.run_bind'', constW_Id]
  have hk : Word32.toNat (Word32.ofNat k) = k % 2 ^ 32 := Word32.toNat_ofNat k
  have hs1 := toNat_bigSigma1 st.e
  have hs0 := toNat_bigSigma0 st.a
  have hch := Word32.toNat_ch st.e st.f st.g
  have hmj := Word32.toNat_maj st.a st.b st.c
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := stateNat_get st
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := sha256Round_get (stateNat st) k (Word32.toNat w)
  simp only [T1, T2, g0, g1, g2, g3, g4, g5, g6, g7] at r0 r1 r2 r3 r4 r5 r6 r7
  cases rp.base with
  | some pb =>
    simp only [Id.run_bind'', Id.run_pure'']
    show stateNat ⟨Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w], _, _, _, _], st.a, st.b, st.c,
      Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w], st.d, _, _], st.e, st.f, st.g⟩ = _
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := stateNat_get ⟨Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w],
      Id.run (bigSigma1 (m := Id) st.e), Id.run (WordM.ch (m := Id) st.e st.f st.g), Id.run (bigSigma0 (m := Id) st.a),
      Id.run (WordM.maj (m := Id) st.a st.b st.c)], st.a, st.b, st.c,
      Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w], st.d, Id.run (bigSigma1 (m := Id) st.e),
      Id.run (WordM.ch (m := Id) st.e st.f st.g)], st.e, st.f, st.g⟩
    apply Vector.ext
    intro i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    · rw [n0, r0]
      simp only [Word32.toNat_sumList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ch_Id, maj_Id]
      rw [hk, hs1, hs0, hch, hmj]
      simp only [add32, Nat.reducePow]
      omega
    · rw [n1, r1]
    · rw [n2, r2]
    · rw [n3, r3]
    · rw [n4, r4]
      simp only [Word32.toNat_sumList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ch_Id]
      rw [hk, hs1, hch]
      simp only [add32, Nat.reducePow]
      omega
    · rw [n5, r5]
    · rw [n6, r6]
    · rw [n7, r7]
    · omega
  | none =>
    simp only [Id.run_bind'', Id.run_pure'']
    show stateNat ⟨Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w, Word32.csaCarry st.h (Word32.ofNat k) w,
      _, _, _, _], st.a, st.b, st.c,
      Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w, Word32.csaCarry st.h (Word32.ofNat k) w, st.d, _, _],
      st.e, st.f, st.g⟩ = _
    have hcsa := Word32.csa_sum st.h (Word32.ofNat k) w
    rw [hk] at hcsa
    simp only [Nat.reducePow] at hcsa
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := stateNat_get ⟨Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w,
      Word32.csaCarry st.h (Word32.ofNat k) w, Id.run (bigSigma1 (m := Id) st.e), Id.run (WordM.ch (m := Id) st.e st.f st.g),
      Id.run (bigSigma0 (m := Id) st.a), Id.run (WordM.maj (m := Id) st.a st.b st.c)], st.a, st.b, st.c,
      Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w, Word32.csaCarry st.h (Word32.ofNat k) w, st.d,
      Id.run (bigSigma1 (m := Id) st.e), Id.run (WordM.ch (m := Id) st.e st.f st.g)], st.e, st.f, st.g⟩
    apply Vector.ext
    intro i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    · rw [n0, r0]
      simp only [Word32.toNat_sumList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ch_Id, maj_Id]
      rw [hs1, hs0, hch, hmj]
      simp only [add32, Nat.reducePow]
      omega
    · rw [n1, r1]
    · rw [n2, r2]
    · rw [n3, r3]
    · rw [n4, r4]
      simp only [Word32.toNat_sumList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, ch_Id]
      rw [hs1, hch]
      simp only [add32, Nat.reducePow]
      omega
    · rw [n5, r5]
    · rw [n6, r6]
    · rw [n7, r7]
    · omega

/-- The round constants, as the specification's. -/
theorem kList_getD : ∀ i : Fin 64, kList.getD i 0 = (Specs.SHA256.K[i]).toNat := by decide

/-- One round of the fold, on the spec's data. -/
theorem round_step (W : List Word32) (hW : W.length = 64) (ms : Vector ℕ 64)
    (hms : ∀ i (hi : i < 64), Word32.toNat (W[i]'(by omega)) = ms[i]) (rps : List RoundPlan) (hrps : rps.length = 64)
    (t : Nat) (ht : t < 64) (st : State GF2) :
    stateNat (Id.run (round (m := Id) st
      ((List.zip kList (List.zip W rps)).getD t (0, Word32.ofNat 0, ⟨none, dfltSum, dfltSum⟩))))
      = Specs.SHA256.sha256Round (stateNat st) (Specs.SHA256.K[(⟨t, ht⟩ : Fin 64)]).toNat ms[t] := by
  have hk64 : kList.length = 64 := rfl
  have hlen : (List.zip kList (List.zip W rps)).length = 64 := by
    rw [List.length_zip, List.length_zip, hW, hrps, hk64]
    rfl
  rw [List.getD_eq_getElem _ _ (by omega), List.getElem_zip, List.getElem_zip, round_spec]
  have hkt := kList_getD ⟨t, ht⟩
  rw [List.getD_eq_getElem _ _ (by rw [hk64]; omega)] at hkt
  rw [hkt, hms t ht]

theorem rounds_spec (W : List Word32) (hW : W.length = 64) (ms : Vector ℕ 64)
    (hms : ∀ i (hi : i < 64), Word32.toNat (W[i]'(by omega)) = ms[i]) (rps : List RoundPlan) (hrps : rps.length = 64)
    (st0 : State GF2) :
    stateNat (Id.run (foldM (round (m := Id)) st0 (List.zip kList (List.zip W rps))))
      = Specs.SHA256.sha256Compress (stateNat st0) ms := by
  rw [foldM_Id, Specs.SHA256.sha256Compress, finFoldl_eq_iter,
    foldl_eq_iter _ (0, Word32.ofNat 0, ⟨none, dfltSum, dfltSum⟩)]
  have hk64 : kList.length = 64 := rfl
  have hlen : (List.zip kList (List.zip W rps)).length = 64 := by
    rw [List.length_zip, List.length_zip, hW, hrps, hk64]
    rfl
  rw [hlen]
  have key : ∀ t, t ≤ 64 → stateNat (iter (fun i st => Id.run (round (m := Id) st
      ((List.zip kList (List.zip W rps)).getD i (0, Word32.ofNat 0, ⟨none, dfltSum, dfltSum⟩)))) t st0)
      = iter (fun i s => if h : i < 64 then Specs.SHA256.sha256Round s (Specs.SHA256.K[(⟨i, h⟩ : Fin 64)]).toNat ms[i]
          else s) t (stateNat st0) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      show stateNat (Id.run (round (m := Id) (iter _ t st0) _)) = (if h : t < 64 then _ else _)
      rw [dif_pos (show t < 64 by omega), round_step W hW ms hms rps hrps t (by omega), ih (by omega)]
  exact key 64 (le_refl _)

/-! ## The whole -/

/-- The output words of a state. -/
theorem stateNat_outs (st : State GF2) (i : Fin 8) :
    (stateNat st)[i] = Word32.toNat (consFin st.a (consFin st.b (consFin st.c (consFin st.d
      (consFin st.e (consFin st.f (consFin st.g (consFin st.h fun i => i.elim0))))))) i) := by
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := stateNat_get st
  fin_cases i
  · exact g0
  · exact g1
  · exact g2
  · exact g3
  · exact g4
  · exact g5
  · exact g6
  · exact g7

theorem compress_val (plan : BlockPlan) (H : Fin 8 → Word32) (block : Fin 16 → Word32) :
    Id.run (Compress.compress (m := Id) plan H block)
      = wordsBits (Specs.SHA256.compressBlock (wordsNat H) (wordsNat block)) := by
  simp only [Compress.compress, Id.run_bind'', constW_Id]
  have hs := schedule_SI (wordsNat block) (Word32.ofNat 0) (schedulePlans plan) (by simp [schedulePlans])
    (finList 16 block) (finList_SI _ block rfl)
  obtain ⟨hlen, hval⟩ := hs
  have hr := rounds_spec _ hlen (sched (wordsNat block) 48) (fun i hi => hval i (by omega) (by omega) hi)
    (roundPlans plan) (by simp [roundPlans]) ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩
  rw [← messageSchedule_eq] at hr
  have hst0 : stateNat ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩ = wordsNat H := by
    apply Vector.ext
    intro i hi
    obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := stateNat_get ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    · rw [g0]; simp [wordsNat]
    · rw [g1]; simp [wordsNat]
    · rw [g2]; simp [wordsNat]
    · rw [g3]; simp [wordsNat]
    · rw [g4]; simp [wordsNat]
    · rw [g5]; simp [wordsNat]
    · rw [g6]; simp [wordsNat]
    · rw [g7]; simp [wordsNat]
    · omega
  rw [hst0] at hr
  funext i
  rw [vecM_Id]
  show Word32.add (H i) _ = _
  have hcb : (Specs.SHA256.compressBlock (wordsNat H) (wordsNat block))[i]
      = add32 ((wordsNat H)[i]) ((Specs.SHA256.sha256Compress (wordsNat H) (Specs.SHA256.messageSchedule (wordsNat block)))[i]) := by
    simp only [Specs.SHA256.compressBlock, Vector.mapFinRange, Fin.getElem_fin, Vector.getElem_ofFn]
  have hHi : (wordsNat H)[i] = Word32.toNat (H i) := by simp [wordsNat]
  simp only [wordsBits, hcb, ← hr, stateNat_outs, Word32.add, hHi]

end Compress

end WeftChals
