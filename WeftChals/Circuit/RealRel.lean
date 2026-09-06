import WeftChals.Circuit.GadgetRel
import WeftChals.Circuit.HybRel

/-!
# The realisation bodies, related along a `BitRel`
-/
namespace WeftChals

universe u v
variable {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] {ρ : Rel m₁ m₂}
  {S₁ S₂ : Type} [BitM m₁ S₁] [BitM m₂ S₂] {f : S₁ → S₂} (h : BitRel ρ f)
include h

namespace BitRel

theorem chReal (x y z : Wd S₁) :
    ρ.R (Wd.map f) (WeftChals.chReal x y z) (WeftChals.chReal (Wd.map f x) (Wd.map f y) (Wd.map f z)) := by
  simp only [WeftChals.chReal]
  exact ρ.bind (h.wordCh (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)) fun w => h.wordMaterialize w

theorem majReal (x y z : Wd S₁) :
    ρ.R (Wd.map f) (WeftChals.majReal x y z) (WeftChals.majReal (Wd.map f x) (Wd.map f y) (Wd.map f z)) := by
  simp only [WeftChals.majReal]
  exact ρ.bind (h.wordMaj (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)) fun w => h.wordMaterialize w

theorem csaReal (x y z : Wd S₁) :
    ρ.R (Prod.map (Wd.map f) (Wd.map f)) (WeftChals.csaReal x y z)
      (WeftChals.csaReal (Wd.map f x) (Wd.map f y) (Wd.map f z)) := by
  simp only [WeftChals.csaReal]
  refine ρ.bind (h.csa3 (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)) fun r => ?_
  refine ρ.bind (h.wordMaterialize r.1) fun s => ?_
  refine ρ.bind (h.wordMaterialize r.2) fun c => ?_
  exact ρ.pure' rfl

theorem addReal (net : Net) (x y : Wd S₁) :
    ρ.R (Wd.map f) (WeftChals.addReal net x y) (WeftChals.addReal net (Wd.map f x) (Wd.map f y)) := by
  simp only [WeftChals.addReal]
  exact ρ.bind (h.add net (Word.ofShares x) (Word.ofShares y)) fun w => h.wordMaterialize w

theorem sumReal (plan : SumPlan) (ws : List (Wd S₁)) :
    ρ.R (Wd.map f) (WeftChals.sumReal plan ws) (WeftChals.sumReal plan (ws.map (Wd.map f))) := by
  simp only [WeftChals.sumReal]
  have e : (ws.map (Wd.map f)).map Word.ofShares = (ws.map Word.ofShares).map (Word.map f) := by
    simp only [List.map_map]
    rfl
  rw [e]
  exact ρ.bind (h.sum plan (ws.map Word.ofShares)) fun w => h.wordMaterialize w

end BitRel

end WeftChals
