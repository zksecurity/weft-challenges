import WeftChals.Circuit.Real
import WeftChals.Circuit.Instances
import WeftChals.Functionality.Word

/-!
# Word-level circuits, generically

The compression function is written over a monad offering the word
operations; the instances are the weft program over `Hyb`, the ideal
values, the timing model (the word gadgets on shares, counted) and the
view of `Hyb`.
-/
namespace WeftChals
open Weft

universe u

/-- The word operations, over the linear bit operations. -/
class WordM (m : Type → Type u) (S : outParam Type) extends LinM m S where
  ch : Wd S → Wd S → Wd S → m (Wd S)
  maj : Wd S → Wd S → Wd S → m (Wd S)
  csa : Wd S → Wd S → Wd S → m (Wd S × Wd S)
  add : Net → Wd S → Wd S → m (Wd S)
  sum : SumPlan → List (Wd S) → m (Wd S)

instance progWordM {fs : Hybrid} {D : Domain} [Has (Lin GF2) fs] [Has Ch32 fs] [Has Maj32 fs] [Has Csa3 fs]
    [Has Add32 fs] [Has Sum32 fs] : WordM (Prog fs.ops D) (D.share GF2) where
  ch x y z := Prog.op (F := Ch32) ⟨(), (x, y, z, ())⟩
  maj x y z := Prog.op (F := Maj32) ⟨(), (x, y, z, ())⟩
  csa x y z := Prog.op (F := Csa3) ⟨(), (x, y, z, ())⟩
  add net x y := Prog.op (F := Add32) ⟨net, (x, y, ())⟩
  sum plan ws := Prog.op (F := Sum32) ⟨plan, (ws, ())⟩

instance valWordM : WordM Id GF2 where
  ch x y z := pure (Word32.ch x y z)
  maj x y z := pure (Word32.maj x y z)
  csa x y z := pure (Word32.csaSum x y z, Word32.csaCarry x y z)
  add _ x y := pure (Word32.add x y)
  sum _ ws := pure (Word32.sumList ws)

/-- The timing of the word operations is the timing of their gadgets. -/
instance timeWordM : WordM Count Nat where
  ch := chReal
  maj := majReal
  csa := csaReal
  add := addReal
  sum := sumReal

/-- A blank word: what the adversary sees of a shared word. -/
def blankW : Fin 32 → Unit := fun _ => ()

instance viewWordM : WordM (Log (Event Hyb.ops)) Unit where
  bxor _ _ := ((), [⟨Hyb.lin .add, ((), (), ()), (), ()⟩])
  bconst b := ((), [⟨Hyb.lin .const, (GF2.ofBool b, ()), (), ()⟩])
  ch _ _ _ := (blankW, [⟨Hyb.ch, (blankW, blankW, blankW, ()), blankW, ()⟩])
  maj _ _ _ := (blankW, [⟨Hyb.maj, (blankW, blankW, blankW, ()), blankW, ()⟩])
  csa _ _ _ := ((blankW, blankW), [⟨Hyb.csa, (blankW, blankW, blankW, ()), (blankW, blankW), ()⟩])
  add net _ _ := (blankW, [⟨Hyb.add net, (blankW, blankW, ()), blankW, ()⟩])
  sum plan ws := (blankW, [⟨Hyb.sum plan, (ws, ()), blankW, ()⟩])

end WeftChals
