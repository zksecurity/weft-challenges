import WeftChals.Circuit.Compress
import WeftChals.Functionality.Compress
import WeftChals.Sem.UInt32
import WeftChals.Sem.Value

/-!
# The compression program computes Wychelean’s `compress`

At the ideal word operations, the program over `Hyb` is the specification:
the schedule fills the message schedule, each round is Wychelean’s `round`, and
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

theorem toUInt32_sigma0 (x : Word32) : Word32.toUInt32 (Id.run (sigma0 (m := Id) x)) = Wychelean.Hashes.SHA256.lowerSigma0 (Word32.toUInt32 x) := by
  simp only [sigma0, Id.run_bind'', shrW_Id, xor3W_Id, rotrW, Wychelean.Hashes.SHA256.lowerSigma0]
  rw [Word32.toUInt32_xor (fun i => x _ + x _) _, Word32.toUInt32_xor, Word32.toUInt32_rotr, Word32.toUInt32_rotr, Word32.toUInt32_shr _ _ (by decide)]
  rfl

theorem toUInt32_sigma1 (x : Word32) : Word32.toUInt32 (Id.run (sigma1 (m := Id) x)) = Wychelean.Hashes.SHA256.lowerSigma1 (Word32.toUInt32 x) := by
  simp only [sigma1, Id.run_bind'', shrW_Id, xor3W_Id, rotrW, Wychelean.Hashes.SHA256.lowerSigma1]
  rw [Word32.toUInt32_xor (fun i => x _ + x _) _, Word32.toUInt32_xor, Word32.toUInt32_rotr, Word32.toUInt32_rotr, Word32.toUInt32_shr _ _ (by decide)]
  rfl

theorem toUInt32_bigSigma0 (x : Word32) :
    Word32.toUInt32 (Id.run (bigSigma0 (m := Id) x)) = Wychelean.Hashes.SHA256.upperSigma0 (Word32.toUInt32 x) := by
  simp only [bigSigma0, xor3W_Id, rotrW, Wychelean.Hashes.SHA256.upperSigma0]
  rw [Word32.toUInt32_xor (fun i => x _ + x _) _, Word32.toUInt32_xor, Word32.toUInt32_rotr, Word32.toUInt32_rotr, Word32.toUInt32_rotr]

theorem toUInt32_bigSigma1 (x : Word32) :
    Word32.toUInt32 (Id.run (bigSigma1 (m := Id) x)) = Wychelean.Hashes.SHA256.upperSigma1 (Word32.toUInt32 x) := by
  simp only [bigSigma1, xor3W_Id, rotrW, Wychelean.Hashes.SHA256.upperSigma1]
  rw [Word32.toUInt32_xor (fun i => x _ + x _) _, Word32.toUInt32_xor, Word32.toUInt32_rotr, Word32.toUInt32_rotr, Word32.toUInt32_rotr]

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

/-- The first `t` entries of Wychelean's schedule have been filled. -/
def sched (blk : Vector UInt32 16) : Nat → Vector UInt32 64
  | 0 => Vector.replicate 64 0
  | t + 1 => if ht : t < 64 then
      (sched blk t).set t (if hb : t < 16 then blk[t] else
        Wychelean.Hashes.SHA256.lowerSigma1 (sched blk t)[t - 2] + (sched blk t)[t - 7] +
        Wychelean.Hashes.SHA256.lowerSigma0 (sched blk t)[t - 15] + (sched blk t)[t - 16])
    else sched blk t

/-- The recursive schedule is exactly Wychelean's `Nat.fold`. -/
theorem messageSchedule_eq (blk : Vector UInt32 16) :
    Wychelean.Hashes.SHA256.messageSchedule blk = sched blk 64 := by
  have key : ∀ (n : Nat) (hn : n ≤ 64),
      Nat.fold n (fun t ht (W : Vector UInt32 64) =>
        W.set t (if hb : t < 16 then blk[t] else
          Wychelean.Hashes.SHA256.lowerSigma1 W[t - 2] + W[t - 7] +
          Wychelean.Hashes.SHA256.lowerSigma0 W[t - 15] + W[t - 16]))
        (Vector.replicate 64 0) = sched blk n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [Nat.fold_succ, sched, dite_eq_left (show n < 64 by omega), ih (by omega)]
  exact key 64 (by omega)

/-- Once written, a schedule entry is unchanged by later steps. -/
theorem sched_get_lt (blk : Vector UInt32 16) (n t i : Nat) (hi : i < 64)
    (hit : i < t) (htn : t ≤ n) : (sched blk n)[i] = (sched blk t)[i] := by
  induction n with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    rfl
  | succ n ih =>
    by_cases h : t = n + 1
    · subst t; rfl
    · have hn : t ≤ n := by omega
      rw [sched]
      split
      · rw [Vector.getElem_set_ne _ _ (by omega), ih hn]
      · exact ih hn

theorem sched_initial (blk : Vector UInt32 16) (i : Nat) (hi : i < 16) :
    (sched blk 16)[i] = blk[i] := by
  rw [sched_get_lt blk 16 (i + 1) i (by omega) (by omega) (by omega)]
  simp [sched, show i < 64 by omega, hi]

theorem sched_succ_last (blk : Vector UInt32 16) (t : Nat) (ht : t < 48) :
    (sched blk (16 + t + 1))[16 + t]'(by omega) =
      Wychelean.Hashes.SHA256.lowerSigma1 ((sched blk (16 + t))[16 + t - 2]'(by omega)) +
      ((sched blk (16 + t))[16 + t - 7]'(by omega)) +
      Wychelean.Hashes.SHA256.lowerSigma0 ((sched blk (16 + t))[16 + t - 15]'(by omega)) +
      ((sched blk (16 + t))[16 + t - 16]'(by omega)) := by
  simp [sched, show 16 + t < 64 by omega, show ¬16 + t < 16 by omega]

/-- The circuit's schedule agrees with the filled part of Wychelean's schedule. -/
def SI (blk : Vector UInt32 16) (t : Nat) (W : List Word32) : Prop :=
  W.length = 16 + t ∧ ∀ i (hi : i < 16 + t) (hW : i < W.length) (h64 : i < 64),
    Word32.toUInt32 W[i] = (sched blk (16 + t))[i]

theorem scheduleStep_SI (blk : Vector UInt32 16) (zero : Word32) (t : Nat) (ht : t < 48)
    (W : List Word32) (p : SumPlan) (h : SI blk t W) :
    SI blk (t + 1) (Id.run (scheduleStep (m := Id) zero W p)) := by
  obtain ⟨hlen, hval⟩ := h
  simp only [scheduleStep, Id.run_bind'', Id.run_pure'']
  have hW : ∀ j (hj : j < 16 + t), W.getD j zero = W[j]'(by omega) := fun j hj =>
    List.getD_eq_getElem _ _ (by omega)
  refine ⟨by rw [List.length_append, hlen]; rfl, fun i hi hW' h64 => ?_⟩
  rcases Nat.lt_or_ge i (16 + t) with hlt | hge
  · rw [List.getElem_append_left (by omega), hval i hlt (by omega) h64]
    exact (sched_get_lt blk _ _ i h64 hlt (by omega)).symm
  · have hi' : i = 16 + t := by omega
    subst hi'
    rw [List.getElem_append_right (by omega), List.getElem_singleton]
    rw [show 16 + (t + 1) = 16 + t + 1 by omega, sched_succ_last blk t ht]
    show Word32.toUInt32 (Word32.sumList _) = _
    simp only [Word32.toUInt32_sumList_cons, Word32.toUInt32_sumList_nil, hlen]
    rw [hW (16 + t - 2) (by omega), hW (16 + t - 7) (by omega),
      hW (16 + t - 15) (by omega), hW (16 + t - 16) (by omega),
      toUInt32_sigma1, toUInt32_sigma0, hval _ (by omega) (by omega) (by omega),
      hval _ (by omega) (by omega) (by omega), hval _ (by omega) (by omega) (by omega),
      hval _ (by omega) (by omega) (by omega)]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, UInt32.toNat_ofNat]
    omega

theorem schedule_SI (blk : Vector UInt32 16) (zero : Word32) (ps : List SumPlan) (hps : ps.length = 48)
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

theorem finList_SI (blk : Vector UInt32 16) (block : Fin 16 → Word32) (hblk : blk = wordsUInt32 block) :
    SI blk 0 (finList 16 block) := by
  rw [finList_eq_ofFn]
  refine ⟨by simp, fun i hi hW h64 => ?_⟩
  rw [List.getElem_ofFn, sched_initial blk i (by omega), hblk]
  simp [wordsUInt32]

/-! ## The rounds -/

/-- Read the circuit's eight working words. -/
def stateWords (st : State GF2) : Vector UInt32 8 :=
  #v[Word32.toUInt32 st.a, Word32.toUInt32 st.b, Word32.toUInt32 st.c, Word32.toUInt32 st.d,
     Word32.toUInt32 st.e, Word32.toUInt32 st.f, Word32.toUInt32 st.g, Word32.toUInt32 st.h]

/-- The entries of a vector literal (with the entries abstract, so that the
kernel never evaluates them). -/
theorem vec8_get {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[0] = a0 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[1] = a1 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[2] = a2 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[3] = a3 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[4] = a4 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[5] = a5 ∧
    (#v[a0, a1, a2, a3, a4, a5, a6, a7])[6] = a6 ∧ (#v[a0, a1, a2, a3, a4, a5, a6, a7])[7] = a7 := by
  simp

/-- The specification's `T1`. -/
def T1 (state : Vector UInt32 8) (k w : UInt32) : UInt32 :=
  state[7] + Wychelean.Hashes.SHA256.upperSigma1 state[4] + Wychelean.Hashes.SHA256.Ch state[4] state[5] state[6] + k + w
/-- The specification's `T2`. -/
def T2 (state : Vector UInt32 8) : UInt32 :=
  Wychelean.Hashes.SHA256.upperSigma0 state[0] + Wychelean.Hashes.SHA256.Maj state[0] state[1] state[2]

theorem sha256Round_lit (state : Vector UInt32 8) (k w : UInt32) :
    SHA256.roundWords state k w = #v[(T1 state k w + T2 state), state[0], state[1], state[2],
      (state[3] + T1 state k w), state[4], state[5], state[6]] := rfl

/-- The entries of the specification's round. -/
theorem sha256Round_get (state : Vector UInt32 8) (k w : UInt32) :
    (SHA256.roundWords state k w)[0] = (T1 state k w + T2 state) ∧
    (SHA256.roundWords state k w)[1] = state[0] ∧ (SHA256.roundWords state k w)[2] = state[1] ∧
    (SHA256.roundWords state k w)[3] = state[2] ∧
    (SHA256.roundWords state k w)[4] = (state[3] + T1 state k w) ∧
    (SHA256.roundWords state k w)[5] = state[4] ∧ (SHA256.roundWords state k w)[6] = state[5] ∧
    (SHA256.roundWords state k w)[7] = state[6] := by
  rw [sha256Round_lit]
  exact vec8_get _ _ _ _ _ _ _ _

theorem stateWords_get (st : State GF2) :
    (stateWords st)[0] = Word32.toUInt32 st.a ∧ (stateWords st)[1] = Word32.toUInt32 st.b ∧ (stateWords st)[2] = Word32.toUInt32 st.c ∧
    (stateWords st)[3] = Word32.toUInt32 st.d ∧ (stateWords st)[4] = Word32.toUInt32 st.e ∧ (stateWords st)[5] = Word32.toUInt32 st.f ∧
    (stateWords st)[6] = Word32.toUInt32 st.g ∧ (stateWords st)[7] = Word32.toUInt32 st.h := by
  simp only [stateWords, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ, and_self]

theorem round_spec (st : State GF2) (k : Nat) (w : Word32) (rp : RoundPlan) :
    stateWords (Id.run (round (m := Id) st (k, w, rp))) = SHA256.roundWords (stateWords st) k.toUInt32 (Word32.toUInt32 w) := by
  simp only [round, Id.run_bind'', constW_Id]
  have hk := Word32.toUInt32_ofNat k
  have hs1 := toUInt32_bigSigma1 st.e
  have hs0 := toUInt32_bigSigma0 st.a
  have hch := Word32.toUInt32_ch st.e st.f st.g
  have hmj := Word32.toUInt32_maj st.a st.b st.c
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := stateWords_get st
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7⟩ := sha256Round_get (stateWords st) k.toUInt32 (Word32.toUInt32 w)
  simp only [T1, T2, g0, g1, g2, g3, g4, g5, g6, g7] at r0 r1 r2 r3 r4 r5 r6 r7
  cases rp.base with
  | some pb =>
    simp only [Id.run_bind'', Id.run_pure'']
    show stateWords ⟨Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w], _, _, _, _], st.a, st.b, st.c,
      Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w], st.d, _, _], st.e, st.f, st.g⟩ = _
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := stateWords_get ⟨Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w],
      Id.run (bigSigma1 (m := Id) st.e), Id.run (WordM.ch (m := Id) st.e st.f st.g), Id.run (bigSigma0 (m := Id) st.a),
      Id.run (WordM.maj (m := Id) st.a st.b st.c)], st.a, st.b, st.c,
      Word32.sumList [Word32.sumList [st.h, Word32.ofNat k, w], st.d, Id.run (bigSigma1 (m := Id) st.e),
      Id.run (WordM.ch (m := Id) st.e st.f st.g)], st.e, st.f, st.g⟩
    apply Vector.ext
    intro i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    · rw [n0, r0]
      simp only [Word32.toUInt32_sumList_cons, Word32.toUInt32_sumList_nil, ch_Id, maj_Id]
      rw [hk, hs1, hs0, hch, hmj]
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_ofNat]
      omega
    · rw [n1, r1]
    · rw [n2, r2]
    · rw [n3, r3]
    · rw [n4, r4]
      simp only [Word32.toUInt32_sumList_cons, Word32.toUInt32_sumList_nil, ch_Id]
      rw [hk, hs1, hch]
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_ofNat]
      omega
    · rw [n5, r5]
    · rw [n6, r6]
    · rw [n7, r7]
    · omega
  | none =>
    simp only [Id.run_bind'', Id.run_pure'']
    show stateWords ⟨Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w, Word32.csaCarry st.h (Word32.ofNat k) w,
      _, _, _, _], st.a, st.b, st.c,
      Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w, Word32.csaCarry st.h (Word32.ofNat k) w, st.d, _, _],
      st.e, st.f, st.g⟩ = _
    have hcsa := congrArg UInt32.toNat (Word32.toUInt32_csa st.h (Word32.ofNat k) w)
    rw [hk] at hcsa
    simp only [UInt32.toNat_add] at hcsa
    obtain ⟨n0, n1, n2, n3, n4, n5, n6, n7⟩ := stateWords_get ⟨Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w,
      Word32.csaCarry st.h (Word32.ofNat k) w, Id.run (bigSigma1 (m := Id) st.e), Id.run (WordM.ch (m := Id) st.e st.f st.g),
      Id.run (bigSigma0 (m := Id) st.a), Id.run (WordM.maj (m := Id) st.a st.b st.c)], st.a, st.b, st.c,
      Word32.sumList [Word32.csaSum st.h (Word32.ofNat k) w, Word32.csaCarry st.h (Word32.ofNat k) w, st.d,
      Id.run (bigSigma1 (m := Id) st.e), Id.run (WordM.ch (m := Id) st.e st.f st.g)], st.e, st.f, st.g⟩
    apply Vector.ext
    intro i hi
    rcases i with _ | _ | _ | _ | _ | _ | _ | _ | i
    · rw [n0, r0]
      simp only [Word32.toUInt32_sumList_cons, Word32.toUInt32_sumList_nil, ch_Id, maj_Id]
      rw [hs1, hs0, hch, hmj]
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_ofNat]
      omega
    · rw [n1, r1]
    · rw [n2, r2]
    · rw [n3, r3]
    · rw [n4, r4]
      simp only [Word32.toUInt32_sumList_cons, Word32.toUInt32_sumList_nil, ch_Id]
      rw [hs1, hch]
      apply UInt32.toNat_inj.mp
      simp only [UInt32.toNat_add, UInt32.toNat_ofNat]
      omega
    · rw [n5, r5]
    · rw [n6, r6]
    · rw [n7, r7]
    · omega

/-- The circuit's round constants are Wychelean's. -/
theorem kList_getD : ∀ i : Fin 64, kList.getD i 0 = (Wychelean.Hashes.SHA256.K[i]).toNat := by decide

private theorem finFoldl_map {α β : Type} (c : α → β) :
    ∀ (n : Nat) (f : α → Fin n → α) (g : β → Fin n → β) (a : α),
      (∀ a i, c (f a i) = g (c a) i) → c (Fin.foldl n f a) = Fin.foldl n g (c a)
  | 0, _, _, _, _ => rfl
  | n + 1, f, g, a, h => by
    rw [Fin.foldl_succ_last, Fin.foldl_succ_last, h, finFoldl_map c n (fun a i => f a i.castSucc) (fun b i => g b i.castSucc) a (fun a i => h a i.castSucc)]

private theorem roundsWords_eq (st : Vector UInt32 8) (W : Vector UInt32 64) :
    SHA256.roundsWords st W = Fin.foldl 64
      (fun s i => SHA256.roundWords s Wychelean.Hashes.SHA256.K[i] W[i]) st := by
  unfold SHA256.roundsWords Wychelean.Hashes.SHA256.rounds
  rw [finFoldl_map SHA256.stateWords 64 _
    (fun s i => SHA256.roundWords s Wychelean.Hashes.SHA256.K[i] W[i]) _ (by
    intro a i
    simp [SHA256.roundWords])]
  rw [SHA256.stateWords_stateOfWords]

/-- One round of the fold, on the spec's data. -/
theorem round_step (W : List Word32) (hW : W.length = 64) (ms : Vector UInt32 64)
    (hms : ∀ i (hi : i < 64), Word32.toUInt32 (W[i]'(by omega)) = ms[i]) (rps : List RoundPlan) (hrps : rps.length = 64)
    (t : Nat) (ht : t < 64) (st : State GF2) :
    stateWords (Id.run (round (m := Id) st
      ((List.zip kList (List.zip W rps)).getD t (0, Word32.ofNat 0, ⟨none, dfltSum, dfltSum⟩))))
      = SHA256.roundWords (stateWords st) (Wychelean.Hashes.SHA256.K[(⟨t, ht⟩ : Fin 64)]) ms[t] := by
  have hk64 : kList.length = 64 := rfl
  have hlen : (List.zip kList (List.zip W rps)).length = 64 := by
    rw [List.length_zip, List.length_zip, hW, hrps, hk64]
    rfl
  rw [List.getD_eq_getElem _ _ (by omega), List.getElem_zip, List.getElem_zip, round_spec]
  have hkt := kList_getD ⟨t, ht⟩
  rw [List.getD_eq_getElem _ _ (by rw [hk64]; omega)] at hkt
  rw [hkt, hms t ht]
  simp [Nat.toUInt32_eq]

theorem rounds_spec (W : List Word32) (hW : W.length = 64) (ms : Vector UInt32 64)
    (hms : ∀ i (hi : i < 64), Word32.toUInt32 (W[i]'(by omega)) = ms[i]) (rps : List RoundPlan) (hrps : rps.length = 64)
    (st0 : State GF2) :
    stateWords (Id.run (foldM (round (m := Id)) st0 (List.zip kList (List.zip W rps))))
      = SHA256.roundsWords (stateWords st0) ms := by
  rw [foldM_Id, roundsWords_eq, finFoldl_eq_iter,
    foldl_eq_iter _ (0, Word32.ofNat 0, ⟨none, dfltSum, dfltSum⟩)]
  have hk64 : kList.length = 64 := rfl
  have hlen : (List.zip kList (List.zip W rps)).length = 64 := by
    rw [List.length_zip, List.length_zip, hW, hrps, hk64]
    rfl
  rw [hlen]
  have key : ∀ t, t ≤ 64 → stateWords (iter (fun i st => Id.run (round (m := Id) st
      ((List.zip kList (List.zip W rps)).getD i (0, Word32.ofNat 0, ⟨none, dfltSum, dfltSum⟩)))) t st0)
      = iter (fun i s => if h : i < 64 then SHA256.roundWords s (Wychelean.Hashes.SHA256.K[(⟨i, h⟩ : Fin 64)]) ms[i]
          else s) t (stateWords st0) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      show stateWords (Id.run (round (m := Id) (iter _ t st0) _)) = (if h : t < 64 then _ else _)
      rw [dite_eq_left (show t < 64 by omega), round_step W hW ms hms rps hrps t (by omega), ih (by omega)]
  exact key 64 (le_refl _)

/-! ## The whole -/

theorem stateWords_outs (st : State GF2) (i : Fin 8) :
    (stateWords st)[i] = Word32.toUInt32 (consFin st.a (consFin st.b (consFin st.c (consFin st.d
      (consFin st.e (consFin st.f (consFin st.g (consFin st.h fun i => i.elim0))))))) i) := by
  fin_cases i <;> rfl

private theorem compressWords_get (H : Vector UInt32 8) (block : Vector UInt32 16) (i : Fin 8) :
    (SHA256.compressWords H block)[i] = H[i] +
      (SHA256.roundsWords H (Wychelean.Hashes.SHA256.messageSchedule block))[i] := by
  fin_cases i <;> rfl

theorem compress_val (plan : BlockPlan) (H : Fin 8 → Word32) (block : Fin 16 → Word32) :
    Id.run (Compress.compress (m := Id) plan H block) =
      wordsOfUInt32 (SHA256.compressWords (wordsUInt32 H) (wordsUInt32 block)) := by
  simp only [Compress.compress, Id.run_bind'', constW_Id]
  have hs := schedule_SI (wordsUInt32 block) (Word32.ofNat 0) (schedulePlans plan)
    (by simp [schedulePlans]) (finList 16 block) (finList_SI _ block rfl)
  obtain ⟨hlen, hval⟩ := hs
  have hr := rounds_spec _ hlen (sched (wordsUInt32 block) 64)
    (fun i hi => hval i (by omega) (by omega) hi)
    (roundPlans plan) (by simp [roundPlans]) ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩
  rw [← messageSchedule_eq] at hr
  have hst0 : stateWords ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩ = wordsUInt32 H := by
    apply Vector.ext
    intro i hi
    interval_cases i <;> simp [stateWords, wordsUInt32]
  rw [hst0] at hr
  funext i
  rw [vecM_Id]
  show Word32.add (H i) _ = _
  apply Word32.ext_toUInt32
  simp only [wordsOfUInt32, Word32.toUInt32_add, Word32.toUInt32_ofNat,
    Nat.toUInt32_eq, UInt32.ofNat_toNat]
  rw [compressWords_get (wordsUInt32 H) (wordsUInt32 block) i, ← hr, stateWords_outs]
  rw [show (wordsUInt32 H)[i] = Word32.toUInt32 (H i) by simp [wordsUInt32]]

end Compress

end WeftChals
