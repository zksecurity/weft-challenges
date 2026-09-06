import WeftChals.Circuit.Compress
import WeftChals.Functionality.Compress
import WeftChals.Sem.Bits
import WeftChals.Sem.Value

/-!
# The compression program computes `compressBlock`

At the ideal word operations, the program over `Hyb` is the specification.
-/
namespace WeftChals
open Weft

theorem Compress.compress_val (plan : BlockPlan) (H : Fin 8 → Word32) (block : Fin 16 → Word32) :
    Id.run (Compress.compress (m := Id) plan H block)
      = wordsBits (Specs.SHA256.compressBlock (wordsNat H) (wordsNat block)) := by
  sorry

end WeftChals
