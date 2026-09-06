import WeftChals.Bits
import WeftChals.Circuit.Plan

/-!
# Word functionalities

The sub-functionalities the compression function is written against: each
is a deterministic, silent operation on words of shared bits.  `Add32` and
`Sum32` take the *structure* of their implementation (a prefix network, a
compression plan) as the operation, so that a caller chooses the circuit
per call while the meaning stays the sum; the models ignore it.
-/
namespace WeftChals
open Weft

/-- The shape of a shared word. -/
abbrev W : Shape := .vec 32 (.share GF2)

namespace Ch32F
abbrev ops : Interface where
  Op := Unit
  dom _ := [W, W, W]
  cod _ := W
def eval : Model ops .ideal Id := .silent fun ⟨(), (x, y, z, ())⟩ => Word32.ch x y z
end Ch32F

/-- `Ch(x, y, z)` on shared words. -/
abbrev Ch32 : Functionality := .ofEval Ch32F.ops Ch32F.eval
@[simp, weft] theorem Ch32.model_eq : Ch32.model = Ch32F.eval.lift PMF := Functionality.ofEval_model _ _

namespace Maj32F
abbrev ops : Interface where
  Op := Unit
  dom _ := [W, W, W]
  cod _ := W
def eval : Model ops .ideal Id := .silent fun ⟨(), (x, y, z, ())⟩ => Word32.maj x y z
end Maj32F

/-- `Maj(x, y, z)` on shared words. -/
abbrev Maj32 : Functionality := .ofEval Maj32F.ops Maj32F.eval
@[simp, weft] theorem Maj32.model_eq : Maj32.model = Maj32F.eval.lift PMF := Functionality.ofEval_model _ _

namespace Csa3F
abbrev ops : Interface where
  Op := Unit
  dom _ := [W, W, W]
  cod _ := .prod W W
def eval : Model ops .ideal Id := .silent fun ⟨(), (x, y, z, ())⟩ => (Word32.csaSum x y z, Word32.csaCarry x y z)
end Csa3F

/-- Carry-save compression: `x + y + z ≡ s + c (mod 2^32)`. -/
abbrev Csa3 : Functionality := .ofEval Csa3F.ops Csa3F.eval
@[simp, weft] theorem Csa3.model_eq : Csa3.model = Csa3F.eval.lift PMF := Functionality.ofEval_model _ _

namespace Add32F
abbrev ops : Interface where
  Op := Net
  dom _ := [W, W]
  cod _ := W
def eval : Model ops .ideal Id := .silent fun ⟨_, (x, y, ())⟩ => Word32.add x y
end Add32F

/-- Addition modulo `2^32`; the operation names the carry-prefix network. -/
abbrev Add32 : Functionality := .ofEval Add32F.ops Add32F.eval
@[simp, weft] theorem Add32.model_eq : Add32.model = Add32F.eval.lift PMF := Functionality.ofEval_model _ _

namespace Sum32F
abbrev ops : Interface where
  Op := SumPlan
  dom _ := [.list W]
  cod _ := W
def eval : Model ops .ideal Id := .silent fun ⟨_, (ws, ())⟩ => Word32.sumList ws
end Sum32F

/-- The sum of a list of words modulo `2^32`; the operation names the compression plan. -/
abbrev Sum32 : Functionality := .ofEval Sum32F.ops Sum32F.eval
@[simp, weft] theorem Sum32.model_eq : Sum32.model = Sum32F.eval.lift PMF := Functionality.ofEval_model _ _

/-- The hybrid the compression function is written against. -/
abbrev Hyb : Hybrid := [Lin GF2, Ch32, Maj32, Csa3, Add32, Sum32]

namespace Hyb
abbrev lin (o : Lin.Op) : Hyb.ops.Op := ⟨0, o⟩
abbrev ch : Hyb.ops.Op := ⟨1, ()⟩
abbrev maj : Hyb.ops.Op := ⟨2, ()⟩
abbrev csa : Hyb.ops.Op := ⟨3, ()⟩
abbrev add (net : Net) : Hyb.ops.Op := ⟨4, net⟩
abbrev sum (plan : SumPlan) : Hyb.ops.Op := ⟨5, plan⟩

theorem model_eq : Hyb.model = Hyb.eval.lift PMF := by
  apply Hybrid.model_lift
  intro i
  match i with
  | ⟨0, _⟩ => exact Lin.model_eq GF2
  | ⟨1, _⟩ => exact Ch32.model_eq
  | ⟨2, _⟩ => exact Maj32.model_eq
  | ⟨3, _⟩ => exact Csa3.model_eq
  | ⟨4, _⟩ => exact Add32.model_eq
  | ⟨5, _⟩ => exact Sum32.model_eq
  | ⟨n + 6, h⟩ => exact absurd h (by simp)
end Hyb

end WeftChals
