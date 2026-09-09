import WeftChals.Circuit.Sum
import WeftChals.Circuit.Rel
import Mathlib.Data.List.InsertIdx

/-!
# The gadget lemmas: two instances of each gadget are related

For every Boolean-level gadget, its two instantiations along a `BitRel`
are related by the structure map.  Each proof follows the gadget's code
with `Rel.bind` and `Rel.pure`.
-/
namespace WeftChals

universe u v

namespace Adder

variable {S T : Type}

def Env.map (f : S → T) (e : Env S) : Env T := List.map (fun p => (p.1, Bit.map f p.2)) e

@[simp] theorem Env.map_nil (f : S → T) : Env.map f [] = [] := rfl
@[simp] theorem Env.map_cons (f : S → T) (p : (Bool × Nat × Nat) × Bit S) (e : Env S) :
    Env.map f (p :: e) = (p.1, Bit.map f p.2) :: Env.map f e := rfl

theorem Env.find_map (f : S → T) (e : Env S) (key : Bool × Nat × Nat) :
    (e.map f).find key = (e.find key).map (Bit.map f) := by
  induction e with
  | nil => rfl
  | cons p ps ih =>
    simp only [Env.map_cons, Env.find, List.find?_cons] at ih ⊢
    split <;> simp_all

def Ctx.map (f : S → T) (c : Ctx S) : Ctx T := ⟨c.x.map f, c.y.map f, c.pos⟩

@[simp] theorem Ctx.map_x (f : S → T) (c : Ctx S) : (c.map f).x = c.x.map f := rfl
@[simp] theorem Ctx.map_y (f : S → T) (c : Ctx S) : (c.map f).y = c.y.map f := rfl
@[simp] theorem Ctx.map_pos (f : S → T) (c : Ctx S) : (c.map f).pos = c.pos := rfl
theorem Ctx.bit_map (f : S → T) (c : Ctx S) (w : Word S) (k : Nat) :
    (c.map f).bit (w.map f) k = (c.bit w k).map f := rfl


theorem Bit.isZero_map (f : S → T) (x : Bit S) : Bit.isZero (x.map f) = Bit.isZero x := by
  cases x with
  | const b => cases b <;> rfl
  | var _ => rfl

theorem mkCtx_map (f : S → T) (x y : Word S) : mkCtx (x.map f) (y.map f) = (mkCtx x y).map f := by
  simp only [mkCtx, Ctx.map, Word.map, Bit.isZero_map]

theorem carryInto_map (f : S → T) (p0 : Nat) (cs : List (Bit S)) (i : Fin 32) :
    carryInto p0 (cs.map (Bit.map f)) i = (carryInto p0 cs i).map f := by
  simp only [carryInto]
  split
  · rfl
  · split
    · rfl
    · simp [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases cs[i.val - 1 - p0]? <;> rfl

end Adder

variable {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] {ρ : Rel m₁ m₂}
  {S₁ S₂ : Type} [BitM m₁ S₁] [BitM m₂ S₂] {f : S₁ → S₂} (h : BitRel ρ f)
include h

namespace BitRel

theorem wordCh (x y z : Word S₁) : ρ.R (Word.map f) (Word.ch x y z) (Word.ch (x.map f) (y.map f) (z.map f)) :=
  ρ.vecM 32 fun i => h.ch3 (x i) (y i) (z i)

theorem wordMaj (x y z : Word S₁) : ρ.R (Word.map f) (Word.maj x y z) (Word.maj (x.map f) (y.map f) (z.map f)) :=
  ρ.vecM 32 fun i => h.maj3 (x i) (y i) (z i)

theorem csa3 (x y z : Word S₁) :
    ρ.R (Prod.map (Word.map f) (Word.map f)) (Word.csa3 x y z) (Word.csa3 (x.map f) (y.map f) (z.map f)) := by
  simp only [Word.csa3]
  refine ρ.bind (ρ.vecM 32 fun i => ρ.bind (h.toLinRel.xor (x i) (y i)) fun t => h.toLinRel.xor t (z i)) fun s => ?_
  refine ρ.bind (ρ.vecM 32 fun i => ?_) fun c => ρ.pure' rfl
  split
  · exact ρ.pure (Bit.map f) (.const false)
  · exact h.maj3 _ _ _

/-! ### The adder -/

open Adder

/-- The structure map on a wire and an environment. -/
abbrev PE (f : S₁ → S₂) : Bit S₁ × Env S₁ → Bit S₂ × Env S₂ := Prod.map (Bit.map f) (Env.map f)

theorem leafG (c : Ctx S₁) (e : Env S₁) (k : Nat) :
    ρ.R (PE f) (Adder.leafG c e k) (Adder.leafG (c.map f) (e.map f) k) := by
  simp only [Adder.leafG, Env.find_map]
  cases e.find (true, k, k) with
  | some w => exact ρ.pure' rfl
  | none =>
    simp only [Option.map_none]
    refine ρ.bind (h.and (c.bit c.x k) (c.bit c.y k)) fun w => ?_
    exact ρ.pure' rfl

theorem leafP (c : Ctx S₁) (k : Nat) : ρ.R (Bit.map f) (Adder.leafP c k) (Adder.leafP (c.map f) k) :=
  h.toLinRel.xor _ _

theorem rippleG (c : Ctx S₁) (e : Env S₁) (a b : Nat) :
    ρ.R (PE f) (Adder.rippleG c e a b) (Adder.rippleG (c.map f) (e.map f) a b) := by
  simp only [Adder.rippleG]
  refine ρ.bind (h.leafG c e a) fun r => ?_
  refine ρ.bind (ρ.foldM (f := Bit.map f) (fun g k => h.maj3 (c.bit c.x k) (c.bit c.y k) g) _ r.1) fun g => ?_
  exact ρ.pure' rfl

theorem rippleP (c : Ctx S₁) (a b : Nat) : ρ.R (Bit.map f) (Adder.rippleP c a b) (Adder.rippleP (c.map f) a b) := by
  simp only [Adder.rippleP]
  refine ρ.bind (h.leafP c a) fun p => ?_
  exact ρ.foldM (f := Bit.map f) (fun p k => ρ.bind (h.leafP c k) fun q => h.and p q) _ p

theorem getG (c : Ctx S₁) (e : Env S₁) (a b : Nat) :
    ρ.R (PE f) (Adder.getG c e a b) (Adder.getG (c.map f) (e.map f) a b) := by
  simp only [Adder.getG]
  split
  · exact h.leafG c e a
  · rw [Env.find_map]
    cases e.find (true, a, b) with
    | some w => exact ρ.pure' rfl
    | none => exact h.rippleG c e a b

theorem getP (c : Ctx S₁) (e : Env S₁) (a b : Nat) :
    ρ.R (Bit.map f) (Adder.getP c e a b) (Adder.getP (c.map f) (e.map f) a b) := by
  simp only [Adder.getP]
  split
  · exact h.leafP c a
  · rw [Env.find_map]
    cases e.find (false, a, b) with
    | some w => exact ρ.pure' rfl
    | none => exact h.rippleP c a b

theorem prod (c : Ctx S₁) (e : Env S₁) (code : Nat) :
    ρ.R (Env.map f) (Adder.prod c e code) (Adder.prod (c.map f) (e.map f) code) := by
  dsimp only [Adder.prod, Ctx.map]
  split
  · split
    · split
      · refine ρ.bind (h.getG c e _ _) fun lo => ?_
        refine ρ.bind (h.maj3 (c.bit c.x _) (c.bit c.y _) lo.1) fun w => ?_
        exact ρ.pure' rfl
      · refine ρ.bind (h.getG c e _ _) fun hi => ?_
        refine ρ.bind (h.getP c hi.2 _ _) fun phi => ?_
        refine ρ.bind (h.getG c hi.2 _ _) fun lo => ?_
        refine ρ.bind (h.and phi lo.1) fun t => ?_
        refine ρ.bind (h.toLinRel.xor hi.1 t) fun w => ?_
        exact ρ.pure' rfl
    · refine ρ.bind (h.getP c e _ _) fun phi => ?_
      refine ρ.bind (h.getP c e _ _) fun plo => ?_
      refine ρ.bind (h.and phi plo) fun w => ?_
      exact ρ.pure' rfl
  · exact ρ.pure' rfl

theorem carries (c : Ctx S₁) (e : Env S₁) :
    ρ.R (List.map (Bit.map f)) (Adder.carries c e) (Adder.carries (c.map f) (e.map f)) := by
  simp only [Adder.carries, Ctx.map_pos]
  refine ρ.bind (ρ.foldM (f := Prod.map (List.map (Bit.map f)) (Env.map f)) (fun acc k => ?_) _ ([], e)) fun r => ?_
  · refine ρ.bind (h.getG c acc.2 0 k) fun g => ?_
    exact ρ.pure' (by simp [List.map_append])
  · exact ρ.pure' rfl

theorem addWith (net : Net) (c : Ctx S₁) :
    ρ.R (Word.map f) (Adder.addWith net c) (Adder.addWith net (c.map f)) := by
  simp only [Adder.addWith, Ctx.map_pos]
  refine ρ.bind (ρ.foldM (f := Env.map f) (fun e code => h.prod c e code) _ []) fun e => ?_
  refine ρ.bind (h.carries c e) fun cs => ?_
  refine ρ.vecM 32 fun i => ?_
  refine ρ.bind (h.toLinRel.xor (c.x i) (c.y i)) fun p => ?_
  rw [carryInto_map]
  exact h.toLinRel.xor p _

theorem add (net : Net) (x y : Word S₁) :
    ρ.R (Word.map f) (Adder.add net x y) (Adder.add net (x.map f) (y.map f)) := by
  simp only [Adder.add, mkCtx_map]
  exact h.addWith net (mkCtx x y)

/-! ### Multi-operand sums -/

theorem sumStep (ws : List (Word S₁)) (code : Nat) :
    ρ.R (List.map (Word.map f)) (Sum32.step ws code) (Sum32.step (ws.map (Word.map f)) code) := by
  simp only [Sum32.step, List.length_map]
  split
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    have gd : ∀ (n : Nat), (ws[n]?.map (Word.map f)).getD (Word.const 0) = Word.map f (ws[n]?.getD (Word.const 0)) := by
      intro n
      cases ws[n]? <;> rfl
    simp only [gd]
    refine ρ.bind (h.csa3 _ _ _) fun r => ?_
    exact ρ.pure' (by simp [List.map_append, ← List.eraseIdx_map])
  · exact ρ.pure' rfl

theorem finish (net : Net) : ∀ (fuel : Nat) (ws : List (Word S₁)),
    ρ.R (Word.map f) (Sum32.finish net fuel ws) (Sum32.finish net fuel (ws.map (Word.map f)))
  | _, [] => by simp only [Sum32.finish, List.map_nil]; exact ρ.pure' rfl
  | _, [x] => by simp only [Sum32.finish, List.map_cons, List.map_nil]; exact ρ.pure' rfl
  | _, [x, y] => by simp only [Sum32.finish, List.map_cons, List.map_nil]; exact h.add net x y
  | 0, x :: _ :: _ :: _ => by simp only [Sum32.finish, List.map_cons]; exact ρ.pure' rfl
  | fuel + 1, x :: y :: z :: rest => by
    simp only [Sum32.finish, List.map_cons]
    refine ρ.bind (h.csa3 x y z) fun r => ?_
    have := finish net fuel (rest ++ [r.1, r.2])
    simpa [List.map_append, Prod.map_fst, Prod.map_snd] using this

theorem sum (plan : SumPlan) (ws : List (Word S₁)) :
    ρ.R (Word.map f) (Sum32.sum plan ws) (Sum32.sum plan (ws.map (Word.map f))) := by
  simp only [Sum32.sum]
  refine ρ.bind (ρ.foldM (f := List.map (Word.map f)) (fun ws code => h.sumStep ws code) _ ws) fun ws => ?_
  simp only [List.length_map]
  exact h.finish plan.net _ ws

end BitRel

end WeftChals
