import WeftChals.Circuit.HybRel
import WeftChals.Circuit.WordM
import WeftChals.Circuit.Instances

/-!
# The primitive laws of `Hyb`: values and views

The program over `Hyb` relates to the ideal word operations (its output)
and to the logging instance (its view), by weft's `output_op` / `view_op`.
-/
namespace WeftChals
open Weft

namespace Hyb

theorem valRel : WordRel (Rel.ofOutput Hyb.eval) (fun x : Domain.ideal.share GF2 => (x : GF2)) where
  pxor _ _ := rfl
  pconst _ := rfl
  pch _ _ _ := rfl
  pmaj _ _ _ := rfl
  pcsa _ _ _ := rfl
  padd _ _ _ := rfl
  psum p ws := by
    show Word32.sumList ws = Word32.sumList (ws.map fun w => w)
    rw [List.map_id']

theorem viewRel : WordRel (Rel.ofView Hyb.eval) (fun _ : Domain.ideal.share GF2 => ()) where
  pxor _ _ := ⟨rfl, rfl⟩
  pconst _ := ⟨rfl, rfl⟩
  pch _ _ _ := ⟨rfl, rfl⟩
  pmaj _ _ _ := ⟨rfl, rfl⟩
  pcsa _ _ _ := ⟨rfl, rfl⟩
  padd _ _ _ := ⟨rfl, rfl⟩
  psum _ _ := ⟨rfl, rfl⟩

end Hyb

end WeftChals
