import WeftChals.Circuit.Compress
import WeftChals.Circuit.Rel

/-!
# Two instances of the compression program are related

`WordRel` states the primitive laws of two `WordM` instances along a map
of wires; the lemmas follow the program's structure.
-/
namespace WeftChals
open Weft

universe u v

/-- The structure map on a word of shares. -/
def Wd.map {S T : Type} (f : S → T) (w : Wd S) : Wd T := fun i => f (w i)

@[simp] theorem Wd.map_apply {S T : Type} (f : S → T) (w : Wd S) (i : Fin 32) : Wd.map f w i = f (w i) := rfl

theorem consFin_map {n : Nat} {α β : Type} (f : α → β) (a : α) (rest : Fin n → α) (i : Fin (n + 1)) :
    consFin (f a) (fun j => f (rest j)) i = f (consFin a rest i) := by
  refine Fin.cases rfl (fun j => ?_) i
  simp [consFin_succ]

/-- The primitive laws of two `WordM` instances along a map of wires. -/
structure WordRel {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] (ρ : Rel m₁ m₂)
    {S₁ S₂ : Type} [WordM m₁ S₁] [WordM m₂ S₂] (f : S₁ → S₂) : Prop extends LinRel ρ f where
  pch : ∀ x y z, ρ.R (Wd.map f) (WordM.ch x y z) (WordM.ch (Wd.map f x) (Wd.map f y) (Wd.map f z))
  pmaj : ∀ x y z, ρ.R (Wd.map f) (WordM.maj x y z) (WordM.maj (Wd.map f x) (Wd.map f y) (Wd.map f z))
  pcsa : ∀ x y z, ρ.R (Prod.map (Wd.map f) (Wd.map f)) (WordM.csa x y z)
    (WordM.csa (Wd.map f x) (Wd.map f y) (Wd.map f z))
  padd : ∀ net x y, ρ.R (Wd.map f) (WordM.add net x y) (WordM.add net (Wd.map f x) (Wd.map f y))
  psum : ∀ plan ws, ρ.R (Wd.map f) (WordM.sum plan ws) (WordM.sum plan (ws.map (Wd.map f)))

namespace Rel
variable {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] (ρ : Rel m₁ m₂)

/-- Folds over lists related by a map. -/
theorem foldM' {α α' β β' : Type} {f : β → β'} {fa : α → α'} {g : β → α → m₁ β} {g' : β' → α' → m₂ β'}
    (h : ∀ b a, ρ.R f (g b a) (g' (f b) (fa a))) :
    ∀ (l : List α) (b : β), ρ.R f (WeftChals.foldM g b l) (WeftChals.foldM g' (f b) (l.map fa))
  | [], b => ρ.pure f b
  | a :: as, b => by
    simp only [WeftChals.foldM, List.map_cons]
    exact ρ.bind (h b a) fun b' => foldM' h as b'

end Rel

section Pure
variable {S₁ S₂ : Type} (f : S₁ → S₂)
open Compress

theorem rotrW_map (w : Wd S₁) (n : Nat) : Compress.rotrW (Wd.map f w) n = Wd.map f (Compress.rotrW w n) := rfl

theorem getD_map (W : List (Wd S₁)) (zero : Wd S₁) (n : Nat) :
    (W.map (Wd.map f)).getD n (Wd.map f zero) = Wd.map f (W.getD n zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[n]? <;> rfl

/-- The structure map on a state. -/
def stateMap (st : State S₁) : State S₂ :=
  ⟨Wd.map f st.a, Wd.map f st.b, Wd.map f st.c, Wd.map f st.d, Wd.map f st.e, Wd.map f st.f, Wd.map f st.g, Wd.map f st.h⟩

/-- The structure map on a round's argument. -/
def argMap (arg : Nat × Wd S₁ × RoundPlan) : Nat × Wd S₂ × RoundPlan :=
  (arg.1, Wd.map f arg.2.1, arg.2.2)

theorem zip_map (ks : List Nat) (W : List (Wd S₁)) (rs : List RoundPlan) :
    (List.zip ks (List.zip W rs)).map (argMap f) = List.zip ks (List.zip (W.map (Wd.map f)) rs) := by
  simp [argMap, List.zip_map_left, List.zip_map_right]

theorem outs_map (st : State S₁) (i : Fin 8) :
    consFin (Wd.map f st.a) (consFin (Wd.map f st.b) (consFin (Wd.map f st.c) (consFin (Wd.map f st.d)
      (consFin (Wd.map f st.e) (consFin (Wd.map f st.f) (consFin (Wd.map f st.g)
      (consFin (Wd.map f st.h) fun i => i.elim0))))))) i
      = Wd.map f (consFin st.a (consFin st.b (consFin st.c (consFin st.d (consFin st.e (consFin st.f (consFin st.g
      (consFin st.h fun i => i.elim0))))))) i) := by
  fin_cases i <;> rfl

end Pure

namespace WordRel
variable {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] {ρ : Rel m₁ m₂}
  {S₁ S₂ : Type} [WordM m₁ S₁] [WordM m₂ S₂] {f : S₁ → S₂} (h : WordRel ρ f)
include h

open Compress

theorem xorW (x y : Wd S₁) : ρ.R (Wd.map f) (Compress.xorW x y) (Compress.xorW (Wd.map f x) (Wd.map f y)) :=
  ρ.vecM 32 fun i => h.pxor (x i) (y i)

theorem xor3W (x y z : Wd S₁) :
    ρ.R (Wd.map f) (Compress.xor3W x y z) (Compress.xor3W (Wd.map f x) (Wd.map f y) (Wd.map f z)) :=
  ρ.bind (h.xorW x y) fun t => h.xorW t z

theorem shrW (w : Wd S₁) (n : Nat) : ρ.R (Wd.map f) (Compress.shrW w n) (Compress.shrW (Wd.map f w) n) := by
  refine ρ.vecM 32 fun i => ?_
  show ρ.R f (if h : i.val + n < 32 then pure (w ⟨i.val + n, h⟩) else bconst false)
    (if h : i.val + n < 32 then pure (Wd.map f w ⟨i.val + n, h⟩) else bconst false)
  split
  · exact ρ.pure' rfl
  · exact h.pconst false

theorem constW (n : Nat) : ρ.R (Wd.map f) (Compress.constW n : m₁ (Wd S₁)) (Compress.constW n) :=
  ρ.vecM 32 fun i => h.pconst _

theorem sigma0 (x : Wd S₁) : ρ.R (Wd.map f) (Compress.sigma0 x) (Compress.sigma0 (Wd.map f x)) := by
  simp only [Compress.sigma0, rotrW_map]
  exact ρ.bind (h.shrW x 3) fun s => h.xor3W _ _ s

theorem sigma1 (x : Wd S₁) : ρ.R (Wd.map f) (Compress.sigma1 x) (Compress.sigma1 (Wd.map f x)) := by
  simp only [Compress.sigma1, rotrW_map]
  exact ρ.bind (h.shrW x 10) fun s => h.xor3W _ _ s

theorem bigSigma0 (x : Wd S₁) : ρ.R (Wd.map f) (Compress.bigSigma0 x) (Compress.bigSigma0 (Wd.map f x)) := by
  simp only [Compress.bigSigma0, rotrW_map]
  exact h.xor3W _ _ _

theorem bigSigma1 (x : Wd S₁) : ρ.R (Wd.map f) (Compress.bigSigma1 x) (Compress.bigSigma1 (Wd.map f x)) := by
  simp only [Compress.bigSigma1, rotrW_map]
  exact h.xor3W _ _ _

theorem scheduleStep (zero : Wd S₁) (W : List (Wd S₁)) (p : SumPlan) :
    ρ.R (List.map (Wd.map f)) (Compress.scheduleStep zero W p)
      (Compress.scheduleStep (Wd.map f zero) (W.map (Wd.map f)) p) := by
  simp only [Compress.scheduleStep, List.length_map, getD_map f]
  refine ρ.bind (h.sigma1 _) fun s1 => ?_
  refine ρ.bind (h.sigma0 _) fun s0 => ?_
  refine ρ.bind (h.psum p [s1, _, s0, _]) fun w => ?_
  exact ρ.pure' (by simp)

theorem round (st : State S₁) (arg : Nat × Wd S₁ × RoundPlan) :
    ρ.R (stateMap f) (Compress.round st arg) (Compress.round (stateMap f st) (argMap f arg)) := by
  simp only [Compress.round, argMap, stateMap]
  refine ρ.bind (h.constW arg.1) fun k => ?_
  refine ρ.bind (h.bigSigma1 st.e) fun s1 => ?_
  refine ρ.bind (h.pch st.e st.f st.g) fun ch => ?_
  refine ρ.bind (h.bigSigma0 st.a) fun s0 => ?_
  refine ρ.bind (h.pmaj st.a st.b st.c) fun mj => ?_
  cases arg.2.2.base with
  | some pb =>
    refine ρ.bind (h.psum pb [st.h, k, arg.2.1]) fun base => ?_
    refine ρ.bind (h.psum _ [base, s1, ch, s0, mj]) fun na => ?_
    refine ρ.bind (h.psum _ [base, st.d, s1, ch]) fun ne => ?_
    exact ρ.pure' rfl
  | none =>
    refine ρ.bind (h.pcsa st.h k arg.2.1) fun bc => ?_
    refine ρ.bind (h.psum _ [bc.1, bc.2, s1, ch, s0, mj]) fun na => ?_
    refine ρ.bind (h.psum _ [bc.1, bc.2, st.d, s1, ch]) fun ne => ?_
    exact ρ.pure' rfl

theorem compress (plan : BlockPlan) (H : Fin 8 → Wd S₁) (block : Fin 16 → Wd S₁) :
    ρ.R (fun (o : Fin 8 → Wd S₁) i => Wd.map f (o i)) (Compress.compress plan H block)
      (Compress.compress plan (fun i => Wd.map f (H i)) (fun i => Wd.map f (block i))) := by
  simp only [Compress.compress]
  refine ρ.bind (h.constW 0) fun zero => ?_
  have e1 : finList 16 (fun i => Wd.map f (block i)) = (finList 16 block).map (Wd.map f) := by
    rw [finList_map]
    rfl
  rw [e1]
  refine ρ.bind (ρ.foldM (f := List.map (Wd.map f)) (fun W p => h.scheduleStep zero W p) _ _) fun W => ?_
  rw [← zip_map f]
  refine ρ.bind (ρ.foldM' (f := stateMap f) (fa := argMap f) (fun st arg => h.round st arg) _ _) fun st => ?_
  refine ρ.vecM 8 fun i => ?_
  simp only [stateMap]
  rw [outs_map f st i]
  exact h.padd _ (H i) _

end WordRel

end WeftChals
