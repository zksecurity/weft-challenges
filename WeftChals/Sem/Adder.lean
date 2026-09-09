import WeftChals.Sem.AdderSem

/-!
# The carry-prefix adder is addition

For every network, `Adder.add net x y` computes `x + y` modulo `2^32`:
every value the builder stores is the carry or propagate of its range,
whether it came from a production or from the fallback ripple, so the
carries it reads off are the carries of the addition.
-/
namespace WeftChals
open Weft AdderSem

@[simp] theorem Id.run_bind' {α β : Type} (x : Id α) (f : α → Id β) : Id.run (x >>= f) = Id.run (f (Id.run x)) := rfl
@[simp] theorem Id.run_pure' {α : Type} (a : α) : Id.run (pure a : Id α) = a := rfl

namespace Adder

variable (x y : Word GF2)

/-! ## Positions -/

/-- The leading-zero test of `mkCtx`. -/
def zeroAt (i : Nat) : Bool :=
  Bit.isZero (x ⟨i % 32, Nat.mod_lt _ (by decide)⟩) || Bit.isZero (y ⟨i % 32, Nat.mod_lt _ (by decide)⟩)

/-- The first position that may carry. -/
def lead : Nat := ((List.range 31).takeWhile (zeroAt x y)).length

theorem lead_le : lead x y ≤ 31 := by
  have := (List.takeWhile_sublist (l := List.range 31) (zeroAt x y)).length_le
  simpa [lead] using this

theorem takeWhile_eq : (List.range 31).takeWhile (zeroAt x y) = List.range (lead x y) := by
  have hpre := List.takeWhile_prefix (l := List.range 31) (zeroAt x y)
  rw [List.prefix_iff_eq_take] at hpre
  rw [hpre, List.take_range]
  simp only [lead]
  congr 1
  have := lead_le x y
  simp only [lead] at this
  omega

theorem pos_eq : (mkCtx x y).pos = List.range' (lead x y) (31 - lead x y) := by
  have h := List.takeWhile_append_dropWhile (p := zeroAt x y) (l := List.range 31)
  rw [takeWhile_eq, List.range_eq_range', List.range_eq_range'] at h
  obtain ⟨k, hk, h1, h2⟩ := List.range'_eq_append_iff.mp h.symm
  have hlk : lead x y = k := by
    have := congrArg List.length h1
    simpa using this
  show (List.range 31).dropWhile (zeroAt x y) = _
  rw [List.range_eq_range', h2, hlk]
  simp

theorem isZero_val {b : Bit GF2} (h : Bit.isZero b = true) : b.val = 0 := by
  cases b with
  | const c => cases c <;> simp_all [Bit.isZero]
  | var _ => simp [Bit.isZero] at h

theorem lead_zero (i : Nat) (hi : i < lead x y) : g x.val y.val i = 0 := by
  have hmem : i ∈ (List.range 31).takeWhile (zeroAt x y) := by
    rw [takeWhile_eq]; exact List.mem_range.mpr hi
  have hp := List.all_eq_true.mp (List.all_takeWhile (l := List.range 31) (p := zeroAt x y)) i hmem
  simp only [zeroAt, Bool.or_eq_true] at hp
  simp only [g, bit, Word.val_apply]
  rcases hp with hp | hp
  · rw [isZero_val hp]; ring
  · rw [isZero_val hp]; ring

/-! ## Elements and their bits -/

theorem pos_length : (mkCtx x y).pos.length = 31 - lead x y := by rw [pos_eq]; simp

theorem pos_getD (k : Nat) (hk : k < 31 - lead x y) : (mkCtx x y).pos.getD k 0 = lead x y + k := by
  rw [pos_eq, List.getD_eq_getElem _ _ (by simpa), List.getElem_range']
  ring

theorem pos_headD : (mkCtx x y).pos.headD 31 = lead x y := by
  rw [pos_eq]
  rcases Nat.lt_or_ge (lead x y) 31 with h | h
  · rw [show 31 - lead x y = (30 - lead x y) + 1 by omega, List.range'_succ]; rfl
  · have := lead_le x y
    rw [show lead x y = 31 by omega]; rfl

theorem bit_x (k : Nat) (hk : k < 31 - lead x y) :
    ((mkCtx x y).bit (mkCtx x y).x k).val = bit x.val (lead x y + k) := by
  simp only [Ctx.bit, pos_getD x y k hk]
  rfl

theorem bit_y (k : Nat) (hk : k < 31 - lead x y) :
    ((mkCtx x y).bit (mkCtx x y).y k).val = bit y.val (lead x y + k) := by
  simp only [Ctx.bit, pos_getD x y k hk]
  rfl

/-! ## The invariant -/

/-- Every stored range value is the carry or propagate of its range. -/
def Inv (e : Env GF2) : Prop := ∀ q ∈ e, q.1.2.1 ≤ q.1.2.2 ∧ q.1.2.2 < 31 - lead x y ∧
  q.2.val = if q.1.1 then G x.val y.val (lead x y + q.1.2.1) (q.1.2.2 - q.1.2.1)
    else P x.val y.val (lead x y + q.1.2.1) (q.1.2.2 - q.1.2.1)

theorem Inv_nil : Inv x y [] := fun _ h => absurd h (List.not_mem_nil)

theorem Inv_cons {e : Env GF2} (he : Inv x y e) {isG : Bool} {a b : Nat} {w : Bit GF2} (hab : a ≤ b)
    (hb : b < 31 - lead x y)
    (hw : w.val = if isG then G x.val y.val (lead x y + a) (b - a) else P x.val y.val (lead x y + a) (b - a)) :
    Inv x y (((isG, a, b), w) :: e) := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact ⟨hab, hb, hw⟩
  · exact he q hq

theorem find_spec {e : Env GF2} (he : Inv x y e) {isG : Bool} {a b : Nat} {w : Bit GF2}
    (h : Env.find e (isG, a, b) = some w) :
    a ≤ b ∧ b < 31 - lead x y ∧
      w.val = if isG then G x.val y.val (lead x y + a) (b - a) else P x.val y.val (lead x y + a) (b - a) := by
  simp only [Env.find, Option.map_eq_some_iff] at h
  obtain ⟨⟨⟨isG', a', b'⟩, w'⟩, hq, hw⟩ := h
  have hmem := List.mem_of_find?_eq_some hq
  have hp := List.find?_some hq
  simp only [decide_eq_true_eq] at hp
  obtain ⟨rfl, rfl, rfl⟩ := hp
  subst hw
  exact he _ hmem

/-! ## Leaves and ripples -/

section
variable {x y}
local notation "n" => 31 - lead x y
local notation "p0" => lead x y

theorem leafG_val {e : Env GF2} (he : Inv x y e) (k : Nat) (hk : k < n) :
    (Id.run (leafG (m := Id) (mkCtx x y) e k)).1.val = G x.val y.val (p0 + k) 0 ∧
      Inv x y (Id.run (leafG (m := Id) (mkCtx x y) e k)).2 := by
  simp only [leafG]
  cases hf : Env.find e (true, k, k) with
  | some w =>
    obtain ⟨_, _, hw⟩ := find_spec x y he hf
    simp only [ite_true, Nat.sub_self] at hw
    exact ⟨hw, he⟩
  | none =>
    simp only [Id.run_bind', Id.run_pure']
    refine ⟨?_, Inv_cons x y he (le_refl k) hk ?_⟩
    · simp [Bit.val_and, bit_x x y k hk, bit_y x y k hk, G, g]
    · simp [Bit.val_and, bit_x x y k hk, bit_y x y k hk, G, g]

theorem leafP_val (k : Nat) (hk : k < n) :
    (Id.run (leafP (m := Id) (mkCtx x y) k)).val = P x.val y.val (p0 + k) 0 := by
  simp only [leafP, Bit.val_xor, bit_x x y k hk, bit_y x y k hk]
  rfl

theorem foldl_maj (a : Nat) : ∀ (j s : Nat) (v : Bit GF2), a + s + j < n → v.val = G x.val y.val (p0 + a) s →
    (List.foldl (fun g k => Id.run (Bit.maj3 (m := Id) ((mkCtx x y).bit (mkCtx x y).x k)
      ((mkCtx x y).bit (mkCtx x y).y k) g)) v (List.range' (a + s + 1) j)).val = G x.val y.val (p0 + a) (s + j)
  | 0, s, v, _, hv => by simpa using hv
  | j + 1, s, v, hlt, hv => by
    rw [List.range'_succ, List.foldl_cons]
    have := foldl_maj a j (s + 1) (Id.run (Bit.maj3 (m := Id) ((mkCtx x y).bit (mkCtx x y).x (a + s + 1))
      ((mkCtx x y).bit (mkCtx x y).y (a + s + 1)) v)) (by omega) (by
        rw [Bit.val_maj3, bit_x x y _ (by omega), bit_y x y _ (by omega), hv]
        simp only [G, maj]
        rw [show p0 + (a + s + 1) = p0 + a + s + 1 by omega])
    rw [show a + (s + 1) + 1 = a + s + 1 + 1 by omega] at this
    rw [this]
    congr 1
    omega

theorem rippleG_val {e : Env GF2} (he : Inv x y e) (a b : Nat) (hab : a ≤ b) (hb : b < n) :
    (Id.run (rippleG (m := Id) (mkCtx x y) e a b)).1.val = G x.val y.val (p0 + a) (b - a) ∧
      Inv x y (Id.run (rippleG (m := Id) (mkCtx x y) e a b)).2 := by
  simp only [rippleG, Id.run_bind', Id.run_pure', foldM_Id]
  obtain ⟨h1, h2⟩ := leafG_val he a (by omega)
  refine ⟨?_, h2⟩
  have := foldl_maj (x := x) (y := y) a (b - a) 0 (Id.run (leafG (m := Id) (mkCtx x y) e a)).1 (by omega)
    (by simpa using h1)
  simpa using this

theorem foldl_p (a : Nat) : ∀ (j s : Nat) (v : Bit GF2), a + s + j < n → v.val = P x.val y.val (p0 + a) s →
    (List.foldl (fun p k => Id.run (Bit.and (m := Id) p (Id.run (leafP (m := Id) (mkCtx x y) k)))) v
      (List.range' (a + s + 1) j)).val = P x.val y.val (p0 + a) (s + j)
  | 0, s, v, _, hv => by simpa using hv
  | j + 1, s, v, hlt, hv => by
    rw [List.range'_succ, List.foldl_cons]
    have := foldl_p a j (s + 1) (Id.run (Bit.and (m := Id) v (Id.run (leafP (m := Id) (mkCtx x y) (a + s + 1)))))
      (by omega) (by
        rw [Bit.val_and, leafP_val _ (by omega), hv]
        simp only [P]
        rw [show p0 + (a + s + 1) = p0 + a + s + 1 by omega]
        ring)
    rw [show a + (s + 1) + 1 = a + s + 1 + 1 by omega] at this
    rw [this]
    congr 1
    omega

theorem rippleP_val (a b : Nat) (hab : a ≤ b) (hb : b < n) :
    (Id.run (rippleP (m := Id) (mkCtx x y) a b)).val = P x.val y.val (p0 + a) (b - a) := by
  simp only [rippleP, Id.run_bind', foldM_Id]
  have := foldl_p (x := x) (y := y) a (b - a) 0 (Id.run (leafP (m := Id) (mkCtx x y) a)) (by omega)
    (by simpa using leafP_val a (by omega))
  simpa using this

theorem getG_val {e : Env GF2} (he : Inv x y e) (a b : Nat) (hab : a ≤ b) (hb : b < n) :
    (Id.run (getG (m := Id) (mkCtx x y) e a b)).1.val = G x.val y.val (p0 + a) (b - a) ∧
      Inv x y (Id.run (getG (m := Id) (mkCtx x y) e a b)).2 := by
  simp only [getG]
  split
  · rename_i hab'
    subst hab'
    simpa using leafG_val he a hb
  · cases hf : Env.find e (true, a, b) with
    | some w =>
      obtain ⟨_, _, hw⟩ := find_spec x y he hf
      simp only [ite_true] at hw
      exact ⟨hw, he⟩
    | none => exact rippleG_val he a b hab hb

theorem getP_val {e : Env GF2} (he : Inv x y e) (a b : Nat) (hab : a ≤ b) (hb : b < n) :
    (Id.run (getP (m := Id) (mkCtx x y) e a b)).val = P x.val y.val (p0 + a) (b - a) := by
  simp only [getP]
  split
  · rename_i hab'
    subst hab'
    simpa using leafP_val a hb
  · cases hf : Env.find e (false, a, b) with
    | some w =>
      obtain ⟨_, _, hw⟩ := find_spec x y he hf
      rw [ite_eq_right (by decide)] at hw
      exact hw
    | none => exact rippleP_val a b hab hb

/-! ## Productions -/

theorem prod_inv {e : Env GF2} (he : Inv x y e) (code : Nat) :
    Inv x y (Id.run (prod (m := Id) (mkCtx x y) e code)) := by
  simp only [prod, pos_length]
  generalize hd : Prod.decode code = d
  split
  · rename_i hp
    obtain ⟨ham, hmb, hbn⟩ := hp
    split
    · split
      · rename_i hmaj
        simp only [Id.run_bind', Id.run_pure']
        obtain ⟨hlo, hinv⟩ := getG_val he _ _ ham (by omega)
        refine Inv_cons x y hinv (by omega) hbn ?_
        rw [ite_eq_left rfl, Bit.val_maj3, bit_x x y _ hbn, bit_y x y _ hbn, hlo,
          show d.b - d.a = (d.m - d.a) + 1 by omega, G]
        rw [show p0 + d.a + (d.m - d.a) + 1 = p0 + d.b by omega]
        rfl
      · rename_i hmaj
        simp only [Id.run_bind', Id.run_pure']
        obtain ⟨hhi, hinv1⟩ := getG_val he (d.m + 1) d.b (by omega) hbn
        have hphi := getP_val hinv1 (d.m + 1) d.b (by omega) hbn
        obtain ⟨hlo, hinv2⟩ := getG_val hinv1 d.a d.m ham (by omega)
        refine Inv_cons x y hinv2 (by omega) hbn ?_
        rw [ite_eq_left rfl, Bit.val_xor, Bit.val_and, hhi, hphi, hlo]
        have := G_split x.val y.val (p0 + d.a) (d.m - d.a) (d.b - (d.m + 1))
        rw [show d.m - d.a + (d.b - (d.m + 1)) + 1 = d.b - d.a by omega,
          show p0 + d.a + (d.m - d.a) + 1 = p0 + (d.m + 1) by omega] at this
        exact this.symm
    · simp only [Id.run_bind', Id.run_pure']
      have hphi := getP_val he (d.m + 1) d.b (by omega) hbn
      have hplo := getP_val he d.a d.m ham (by omega)
      refine Inv_cons x y he (by omega) hbn ?_
      rw [ite_eq_right Bool.false_ne_true, Bit.val_and, hphi, hplo]
      have := P_split x.val y.val (p0 + d.a) (d.m - d.a) (d.b - (d.m + 1))
      rw [show d.m - d.a + (d.b - (d.m + 1)) + 1 = d.b - d.a by omega,
        show p0 + d.a + (d.m - d.a) + 1 = p0 + (d.m + 1) by omega] at this
      exact this.symm
  · exact he

theorem foldl_prod_inv : ∀ (prods : List Nat) (e : Env GF2), Inv x y e →
    Inv x y (List.foldl (fun e code => Id.run (prod (m := Id) (mkCtx x y) e code)) e prods)
  | [], _, he => he
  | code :: rest, e, he => by
    rw [List.foldl_cons]
    exact foldl_prod_inv rest _ (prod_inv he code)

/-! ## Carries -/

/-- The step of the carries fold. -/
def cstep (acc : List (Bit GF2) × Env GF2) (k : Nat) : List (Bit GF2) × Env GF2 :=
  (acc.1 ++ [(Id.run (getG (m := Id) (mkCtx x y) acc.2 0 k)).1], (Id.run (getG (m := Id) (mkCtx x y) acc.2 0 k)).2)

/-- The carries computed so far are right. -/
def CInv (j : Nat) (acc : List (Bit GF2) × Env GF2) : Prop :=
  acc.1.length = j ∧ (∀ k (hk : k < acc.1.length), (acc.1[k]).val = G x.val y.val p0 k) ∧ Inv x y acc.2

theorem carries_foldl : ∀ (j : Nat) (acc : List (Bit GF2) × Env GF2), j ≤ n → CInv (x := x) (y := y) 0 acc →
    CInv (x := x) (y := y) j (List.foldl (cstep (x := x) (y := y)) acc (List.range j))
  | 0, acc, _, h0 => by simpa using h0
  | j + 1, acc, hj, h0 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hlen, hval, hinv⟩ := carries_foldl j acc (by omega) h0
    generalize hacc : List.foldl (cstep (x := x) (y := y)) acc (List.range j) = acc' at hlen hval hinv
    obtain ⟨hg, hinv'⟩ := getG_val hinv 0 j (Nat.zero_le _) (by omega)
    refine ⟨by simp [cstep, hlen], fun k hk => ?_, hinv'⟩
    simp only [cstep, List.length_append, List.length_singleton, hlen] at hk
    rcases Nat.lt_or_ge k j with hkj | hkj
    · simp only [cstep]
      rw [List.getElem_append_left (by omega)]
      exact hval k (by omega)
    · have hk' : k = j := by omega
      subst hk'
      simp only [cstep]
      rw [List.getElem_append_right (by omega)]
      simpa [hlen] using hg

theorem carries_eq {e : Env GF2} :
    Id.run (carries (m := Id) (mkCtx x y) e) = (List.foldl (cstep (x := x) (y := y)) ([], e) (List.range n)).1 := by
  simp only [carries, Id.run_bind', Id.run_pure', foldM_Id, pos_length]
  rfl

theorem carries_spec {e : Env GF2} (he : Inv x y e) :
    (Id.run (carries (m := Id) (mkCtx x y) e)).length = n ∧
      ∀ k (hk : k < (Id.run (carries (m := Id) (mkCtx x y) e)).length),
        ((Id.run (carries (m := Id) (mkCtx x y) e))[k]).val = G x.val y.val p0 k := by
  rw [carries_eq]
  have := carries_foldl (x := x) (y := y) n ([], e) (le_refl _) ⟨rfl, fun k hk => absurd hk (by simp), he⟩
  exact ⟨this.1, this.2.1⟩

theorem carryInto_val {cs : List (Bit GF2)} (hlen : cs.length = n)
    (hval : ∀ k (hk : k < cs.length), (cs[k]).val = G x.val y.val p0 k) (i : Fin 32) :
    (carryInto p0 cs i).val = if i.val = 0 then 0 else G x.val y.val 0 (i.val - 1) := by
  simp only [carryInto]
  split
  · simp_all
  · rename_i hi0
    split
    · rename_i hlt
      have := G_zero_of_g_zero x.val y.val 0 (p0 - 1) (fun j hj => lead_zero x y j (by omega)) (i.val - 1) (by omega)
      simp [this]
    · rename_i hge
      have hk : i.val - 1 - p0 < cs.length := by have := i.isLt; omega
      rw [List.getD_eq_getElem _ _ hk, hval _ hk]
      rcases Nat.eq_zero_or_pos p0 with hp | hp
      · rw [hp]; simp
      · have := G_split x.val y.val 0 (p0 - 1) (i.val - 1 - p0)
        rw [show p0 - 1 + (i.val - 1 - p0) + 1 = i.val - 1 by omega, show 0 + (p0 - 1) + 1 = p0 by omega,
          G_zero_of_g_zero x.val y.val 0 (p0 - 1) (fun j hj => lead_zero x y j (by omega)) (p0 - 1) (le_refl _)] at this
        rw [this]
        ring

end

/-! ## Addition -/

theorem add_val (net : Net) (x y : Word GF2) :
    (Id.run (Adder.add (m := Id) net x y)).val = Word32.add x.val y.val := by
  funext i
  simp only [Adder.add, addWith, Id.run_bind', foldM_Id, pos_headD]
  have hinv := foldl_prod_inv (x := x) (y := y) (if net.n = (mkCtx x y).pos.length then net.prods else []) []
    (Inv_nil x y)
  obtain ⟨hlen, hval⟩ := carries_spec hinv
  rw [Word.val_apply, vecM_Id]
  show Bit.val (Id.run (Bit.xor (m := Id) (Id.run (Bit.xor (m := Id) (x i) (y i))) (carryInto (lead x y) _ i))) = _
  rw [Bit.val_xor, Bit.val_xor, carryInto_val hlen hval i, add_bit x.val y.val i i.isLt, bit_lt _ _ i.isLt,
    bit_lt _ _ i.isLt]
  rfl

end Adder

end WeftChals
