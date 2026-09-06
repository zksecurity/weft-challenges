import WeftChals.Sem.Adder

/-!
# The word gadgets compute the word operations
-/
namespace WeftChals
open Weft

theorem Word.ch_val (x y z : Word GF2) : (Id.run (Word.ch (m := Id) x y z)).val = Word32.ch x.val y.val z.val := by
  sorry

theorem Word.maj_val (x y z : Word GF2) : (Id.run (Word.maj (m := Id) x y z)).val = Word32.maj x.val y.val z.val := by
  sorry

theorem Word.csa3_val (x y z : Word GF2) :
    (Id.run (Word.csa3 (m := Id) x y z)).1.val = Word32.csaSum x.val y.val z.val ∧
    (Id.run (Word.csa3 (m := Id) x y z)).2.val = Word32.csaCarry x.val y.val z.val := by
  sorry

theorem Sum32.sum_val (plan : SumPlan) (ws : List (Word GF2)) :
    (Id.run (Sum32.sum (m := Id) plan ws)).val = Word32.sumList (ws.map Word.val) := by
  sorry

theorem chReal_val (x y z : Wd GF2) : Id.run (chReal (m := Id) x y z) = Word32.ch x y z := by
  sorry

theorem majReal_val (x y z : Wd GF2) : Id.run (majReal (m := Id) x y z) = Word32.maj x y z := by
  sorry

theorem csaReal_val (x y z : Wd GF2) :
    Id.run (csaReal (m := Id) x y z) = (Word32.csaSum x y z, Word32.csaCarry x y z) := by
  sorry

theorem addReal_val (net : Net) (x y : Wd GF2) : Id.run (addReal (m := Id) net x y) = Word32.add x y := by
  sorry

theorem sumReal_val (plan : SumPlan) (ws : List (Wd GF2)) :
    Id.run (sumReal (m := Id) plan ws) = Word32.sumList ws := by
  sorry

end WeftChals
