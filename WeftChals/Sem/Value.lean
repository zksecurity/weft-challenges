import WeftChals.Circuit.Real
import WeftChals.Circuit.Instances
import WeftChals.Bits

/-!
# The value of a gadget

At `Id` on `GF2` a gadget is a pure function on wires; a wire's value is
its constant or its share, and the folding layer computes exactly the
xor, and, choice and majority of the values.
-/
namespace WeftChals
open Weft

/-- The value of a wire. -/
def Bit.val : Bit GF2 → GF2
  | .const b => GF2.ofBool b
  | .var s => s

@[simp] theorem Bit.val_const (b : Bool) : Bit.val (.const b) = GF2.ofBool b := rfl
@[simp] theorem Bit.val_var (s : GF2) : Bit.val (.var s) = s := rfl

/-- The value of a word of wires. -/
def Word.val (w : Word GF2) : Word32 := fun i => (w i).val

@[simp] theorem Word.val_apply (w : Word GF2) (i : Fin 32) : w.val i = (w i).val := rfl
@[simp] theorem Word.val_ofShares (w : Wd GF2) : (Word.ofShares w).val = w := rfl

@[simp] theorem vecM_Id {α : Type} : ∀ (n : Nat) (g : Fin n → Id α), Id.run (vecM n g) = fun i => Id.run (g i)
  | 0, g => by funext i; exact i.elim0
  | n + 1, g => by
    funext i
    show consFin (Id.run (g 0)) (Id.run (vecM n fun i => g i.succ)) i = Id.run (g i)
    rw [vecM_Id n]
    refine Fin.cases rfl (fun j => ?_) i
    simp [consFin_succ]

@[simp] theorem listM_Id {α β : Type} (f : α → Id β) : ∀ l : List α, Id.run (listM f l) = l.map fun a => Id.run (f a)
  | [] => rfl
  | a :: as => by
    show Id.run (f a) :: Id.run (listM f as) = _
    rw [listM_Id f as]
    rfl

@[simp] theorem foldM_Id {α β : Type} (f : β → α → Id β) : ∀ (l : List α) (b : β),
    Id.run (foldM f b l) = l.foldl (fun b a => Id.run (f b a)) b
  | [], _ => rfl
  | a :: as, b => by
    show Id.run (foldM f (Id.run (f b a)) as) = _
    rw [foldM_Id f as]
    rfl

namespace Bit

theorem ofBool_xor' (a b : Bool) : GF2.ofBool (a ^^ b) = GF2.ofBool a + GF2.ofBool b := GF2.ofBool_xor a b
theorem ofBool_and' (a b : Bool) : GF2.ofBool (a && b) = GF2.ofBool a * GF2.ofBool b := GF2.ofBool_and a b

@[simp] theorem val_share (b : Bool) : Bit.val (Id.run (Bit.share (m := Id) b)) = GF2.ofBool b := rfl

@[simp] theorem val_xor (x y : Bit GF2) : Bit.val (Id.run (Bit.xor (m := Id) x y)) = x.val + y.val := by
  cases x with
  | const a =>
    cases y with
    | const b => simp [Id.run, Bit.xor, GF2.ofBool_xor]
    | var t =>
      cases a
      · show t = 0 + t
        exact (zero_add t).symm
      · show t + 1 = 1 + t
        exact add_comm _ _
  | var s =>
    cases y with
    | const b =>
      cases b
      · show s = s + 0
        exact (add_zero s).symm
      · rfl
    | var t => rfl

@[simp] theorem val_and (x y : Bit GF2) : Bit.val (Id.run (Bit.and (m := Id) x y)) = x.val * y.val := by
  cases x with
  | const a =>
    cases y with
    | const b => simp [Id.run, Bit.and, GF2.ofBool_and]
    | var t => cases a <;> simp [Id.run, Bit.and]
  | var s =>
    cases y with
    | const b => cases b <;> simp [Id.run, Bit.and]
    | var t => rfl

theorem val_ch3 (x y z : Bit GF2) :
    Bit.val (Id.run (Bit.ch3 (m := Id) x y z)) = z.val + x.val * (y.val + z.val) := by
  show Bit.val (Id.run (Bit.xor z (Id.run (Bit.and x (Id.run (Bit.xor y z)))))) = _
  rw [val_xor, val_and, val_xor]

theorem val_maj3 (x y z : Bit GF2) :
    Bit.val (Id.run (Bit.maj3 (m := Id) x y z)) = x.val * y.val + x.val * z.val + y.val * z.val := by
  have generic : ∀ x y z : Bit GF2, Bit.val (Id.run (do
      let t ← Bit.xor (m := Id) x y; let u ← Bit.xor x z; let p ← Bit.and t u; Bit.xor x p))
      = x.val * y.val + x.val * z.val + y.val * z.val := by
    intro x y z
    show Bit.val (Id.run (Bit.xor x (Id.run (Bit.and (Id.run (Bit.xor x y)) (Id.run (Bit.xor x z)))))) = _
    rw [val_xor, val_and, val_xor, val_xor]
    generalize x.val = a; generalize y.val = b; generalize z.val = c
    revert a b c; decide
  cases x with
  | const a =>
    cases y with
    | const b =>
      cases z with
      | const c => cases a <;> cases b <;> cases c <;> decide
      | var s =>
        simp only [Bit.maj3]
        split
        · subst_vars; cases b <;> (revert s; decide)
        · cases a <;> cases b <;> simp_all [Id.run]
    | var s =>
      cases z with
      | const c =>
        simp only [Bit.maj3]
        split
        · subst_vars; cases c <;> (revert s; decide)
        · cases a <;> cases c <;> simp_all [Id.run]
      | var t => exact generic _ _ _
  | var s =>
    cases y with
    | const b =>
      cases z with
      | const c =>
        simp only [Bit.maj3]
        split
        · subst_vars; cases c <;> (revert s; decide)
        · cases b <;> cases c <;> simp_all [Id.run]
      | var t => exact generic _ _ _
    | var t => exact generic _ _ _

@[simp] theorem materialize_Id (x : Bit GF2) : Id.run (Bit.materialize (m := Id) x) = x.val := by
  cases x <;> rfl

end Bit

@[simp] theorem Word.materialize_Id (w : Word GF2) : Id.run (Word.materialize (m := Id) w) = w.val := by
  funext i
  simp [Word.materialize, Word.val]

end WeftChals
