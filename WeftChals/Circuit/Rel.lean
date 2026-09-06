import WeftChals.Circuit.BitM
import WeftChals.Circuit.Writer

/-!
# Relating two instances of a generic gadget

A gadget written over `[Monad m] [BitM m S]` has as many meanings as
there are instances.  A `Rel` between two monads is a relation on
computations (indexed by a map between result types) closed under `pure`
and `bind`; `BitRel` adds the three primitive laws along a map of wires.
A gadget lemma then states that the gadget's two instantiations are
related, and is proved by following the gadget's structure with `Rel.bind`
and `Rel.pure`: the gadget is the same term on both sides.
-/
namespace WeftChals

universe u v

/-- A relation between computations of two monads, closed under the monad operations. -/
structure Rel (m₁ : Type → Type u) (m₂ : Type → Type v) [Monad m₁] [Monad m₂] where
  R : {α β : Type} → (α → β) → m₁ α → m₂ β → Prop
  pure : ∀ {α β : Type} (g : α → β) (a : α), R g (pure a) (pure (g a))
  bind : ∀ {α α' β β' : Type} {g : α → α'} {h : β → β'} {x : m₁ α} {y : m₂ α'} {k : α → m₁ β} {l : α' → m₂ β'},
    R g x y → (∀ a, R h (k a) (l (g a))) → R h (x >>= k) (y >>= l)

namespace Rel
variable {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] (ρ : Rel m₁ m₂)

/-- `pure`, with the image given by an equation. -/
theorem pure' {α β : Type} {g : α → β} {a : α} {b : β} (e : g a = b) :
    ρ.R g (Pure.pure a) (Pure.pure b) :=
  e ▸ ρ.pure g a

theorem vecM {α α' : Type} {f : α → α'} :
    ∀ (n : Nat) {g : Fin n → m₁ α} {g' : Fin n → m₂ α'}, (∀ i, ρ.R f (g i) (g' i)) →
      ρ.R (fun v i => f (v i)) (WeftChals.vecM n g) (WeftChals.vecM n g')
  | 0, g, g', _ => by
    simp only [WeftChals.vecM]
    have := ρ.pure (fun (v : Fin 0 → α) (i : Fin 0) => f (v i)) (fun i => i.elim0)
    refine cast ?_ this
    congr
    funext i
    exact i.elim0
  | n + 1, g, g', h => by
    simp only [WeftChals.vecM]
    refine ρ.bind (h 0) fun a => ?_
    refine ρ.bind (vecM n fun i => h i.succ) fun rest => ?_
    have := ρ.pure (fun (v : Fin (n + 1) → α) (i : Fin (n + 1)) => f (v i)) (consFin a rest)
    refine cast ?_ this
    congr
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [consFin_succ]

theorem listM {α β β' : Type} {f : β → β'} {g : α → m₁ β} {g' : α → m₂ β'} (h : ∀ a, ρ.R f (g a) (g' a)) :
    ∀ l : List α, ρ.R (List.map f) (WeftChals.listM g l) (WeftChals.listM g' l)
  | [] => ρ.pure (List.map f) []
  | a :: as => by
    simp only [WeftChals.listM]
    refine ρ.bind (h a) fun b => ?_
    refine ρ.bind (listM h as) fun bs => ?_
    exact ρ.pure (List.map f) (b :: bs)

theorem foldM {α β β' : Type} {f : β → β'} {g : β → α → m₁ β} {g' : β' → α → m₂ β'}
    (h : ∀ b a, ρ.R f (g b a) (g' (f b) a)) :
    ∀ (l : List α) (b : β), ρ.R f (WeftChals.foldM g b l) (WeftChals.foldM g' (f b) l)
  | [], b => ρ.pure f b
  | a :: as, b => by
    simp only [WeftChals.foldM]
    exact ρ.bind (h b a) fun b' => foldM h as b'

end Rel

/-- The linear primitive laws of two `LinM` instances along a map of wires. -/
structure LinRel {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] (ρ : Rel m₁ m₂)
    {S₁ S₂ : Type} [LinM m₁ S₁] [LinM m₂ S₂] (f : S₁ → S₂) : Prop where
  pxor : ∀ a b, ρ.R f (bxor a b) (bxor (f a) (f b))
  pconst : ∀ b, ρ.R f (bconst b) (bconst b)

/-- The primitive laws of two `BitM` instances along a map of wires. -/
structure BitRel {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] (ρ : Rel m₁ m₂)
    {S₁ S₂ : Type} [BitM m₁ S₁] [BitM m₂ S₂] (f : S₁ → S₂) : Prop extends LinRel ρ f where
  pand : ∀ a b, ρ.R f (band a b) (band (f a) (f b))

namespace LinRel
variable {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] {ρ : Rel m₁ m₂}
  {S₁ S₂ : Type} [LinM m₁ S₁] [LinM m₂ S₂] {f : S₁ → S₂} (h : LinRel ρ f)
include h

theorem share (b : Bool) : ρ.R (Bit.map f) (Bit.share b : m₁ (Bit S₁)) (Bit.share b) := by
  simp only [Bit.share]
  exact ρ.bind (h.pconst b) fun s => ρ.pure (Bit.map f) (.var s)

theorem xor (x y : Bit S₁) : ρ.R (Bit.map f) (Bit.xor x y) (Bit.xor (x.map f) (y.map f)) := by
  cases x with
  | const a =>
    cases y with
    | const b => exact ρ.pure (Bit.map f) (.const (a ^^ b))
    | var t =>
      cases a with
      | false => exact ρ.pure (Bit.map f) (.var t)
      | true =>
        simp only [Bit.xor, Bit.map]
        exact ρ.bind (h.pconst true) fun o => ρ.bind (h.pxor t o) fun r => ρ.pure (Bit.map f) (.var r)
  | var s =>
    cases y with
    | const b =>
      cases b with
      | false => exact ρ.pure (Bit.map f) (.var s)
      | true =>
        simp only [Bit.xor, Bit.map]
        exact ρ.bind (h.pconst true) fun o => ρ.bind (h.pxor s o) fun r => ρ.pure (Bit.map f) (.var r)
    | var t =>
      simp only [Bit.xor, Bit.map]
      exact ρ.bind (h.pxor s t) fun r => ρ.pure (Bit.map f) (.var r)

theorem materialize (x : Bit S₁) : ρ.R f (Bit.materialize x : m₁ S₁) (Bit.materialize (x.map f)) := by
  cases x with
  | const b => exact h.pconst b
  | var s => exact ρ.pure f s

theorem wordXor (x y : Word S₁) : ρ.R (Word.map f) (Word.xor x y) (Word.xor (x.map f) (y.map f)) :=
  ρ.vecM 32 fun i => h.xor (x i) (y i)

theorem wordXor3 (x y z : Word S₁) : ρ.R (Word.map f) (Word.xor3 x y z) (Word.xor3 (x.map f) (y.map f) (z.map f)) :=
  ρ.bind (h.wordXor x y) fun t => h.wordXor t z

theorem wordMaterialize (w : Word S₁) : ρ.R (fun v i => f (v i)) (Word.materialize w : m₁ (Fin 32 → S₁)) (Word.materialize (w.map f)) :=
  ρ.vecM 32 fun i => h.materialize (w i)

end LinRel

namespace BitRel
variable {m₁ : Type → Type u} {m₂ : Type → Type v} [Monad m₁] [Monad m₂] {ρ : Rel m₁ m₂}
  {S₁ S₂ : Type} [BitM m₁ S₁] [BitM m₂ S₂] {f : S₁ → S₂} (h : BitRel ρ f)
include h

theorem and (x y : Bit S₁) : ρ.R (Bit.map f) (Bit.and x y) (Bit.and (x.map f) (y.map f)) := by
  cases x with
  | const a =>
    cases y with
    | const b => exact ρ.pure (Bit.map f) (.const (a && b))
    | var t =>
      cases a with
      | false => exact ρ.pure (Bit.map f) (.const false)
      | true => exact ρ.pure (Bit.map f) (.var t)
  | var s =>
    cases y with
    | const b =>
      cases b with
      | false => exact ρ.pure (Bit.map f) (.const false)
      | true => exact ρ.pure (Bit.map f) (.var s)
    | var t =>
      simp only [Bit.and, Bit.map]
      exact ρ.bind (h.pand s t) fun r => ρ.pure (Bit.map f) (.var r)

theorem ch3 (x y z : Bit S₁) : ρ.R (Bit.map f) (Bit.ch3 x y z) (Bit.ch3 (x.map f) (y.map f) (z.map f)) := by
  simp only [Bit.ch3]
  exact ρ.bind (h.toLinRel.xor y z) fun t => ρ.bind (h.and x t) fun p => h.toLinRel.xor z p

theorem maj3 (x y z : Bit S₁) : ρ.R (Bit.map f) (Bit.maj3 x y z) (Bit.maj3 (x.map f) (y.map f) (z.map f)) := by
  have generic : ∀ x y z : Bit S₁, ρ.R (Bit.map f)
      (do let t ← Bit.xor x y; let u ← Bit.xor x z; let p ← Bit.and t u; Bit.xor x p : m₁ (Bit S₁))
      (do let t ← Bit.xor (x.map f) (y.map f); let u ← Bit.xor (x.map f) (z.map f)
          let p ← Bit.and t u; Bit.xor (x.map f) p) := fun x y z =>
    ρ.bind (h.toLinRel.xor x y) fun t => ρ.bind (h.toLinRel.xor x z) fun u => ρ.bind (h.and t u) fun p => h.toLinRel.xor x p
  cases x with
  | const a =>
    cases y with
    | const b =>
      cases z with
      | const c => exact ρ.pure (Bit.map f) _
      | var s =>
        simp only [Bit.maj3, Bit.map]
        split
        · exact ρ.pure (Bit.map f) (.const a)
        · exact ρ.pure (Bit.map f) (.var s)
    | var s =>
      cases z with
      | const c =>
        simp only [Bit.maj3, Bit.map]
        split
        · exact ρ.pure (Bit.map f) (.const a)
        · exact ρ.pure (Bit.map f) (.var s)
      | var t => exact generic _ _ _
  | var s =>
    cases y with
    | const b =>
      cases z with
      | const c =>
        simp only [Bit.maj3, Bit.map]
        split
        · exact ρ.pure (Bit.map f) (.const b)
        · exact ρ.pure (Bit.map f) (.var s)
      | var t => exact generic _ _ _
    | var t => exact generic _ _ _

end BitRel

end WeftChals
