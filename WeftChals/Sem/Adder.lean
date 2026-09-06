import WeftChals.Sem.Value
import WeftChals.Sem.Bits

/-!
# The carry-prefix adder is addition

For every network, `Adder.add net x y` computes `x + y` modulo `2^32`.
-/
namespace WeftChals
open Weft

theorem Adder.add_val (net : Net) (x y : Word GF2) :
    (Id.run (Adder.add (m := Id) net x y)).val = Word32.add x.val y.val := by sorry

end WeftChals
