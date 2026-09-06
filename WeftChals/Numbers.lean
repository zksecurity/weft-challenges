import WeftChals.Realization.Cost
import WeftChals.Plans.Compression

/-!
# The numbers

For the exported plan: the round complexity and the communication of the
compression function over Boolean circuits, and the perfect privacy of
its realisation.  The timing model is a pure function on ready times,
which the kernel evaluates.
-/
namespace WeftChals
open Weft

/-- The circuit: the exported plan. -/
abbrev plan : BlockPlan := Plans.Compression.plan

/-- Inputs available at round 0. -/
def zeroTimes {k : Nat} : Fin k → Wd Nat := fun _ _ => 0

/-- **Communication**: 38656 ANDs. -/
theorem timeModel_comm : (timeModel plan zeroTimes zeroTimes).2 = 38656 := by decide +kernel

/-- **Round complexity**: the output is ready at round 456. -/
theorem timeModel_ready : maxTime (timeModel plan zeroTimes zeroTimes).1 = 456 := by decide +kernel

/-- The compression function on inputs available at round 0. -/
def request (H : Fin 8 → Word32) (block : Fin 16 → Word32) : Req CompressF.ops .timed :=
  ⟨(), (fun j i => ⟪H j i⟫, fun j i => ⟪block j i⟫, ())⟩

theorem timesOf_request {k : Nat} (ws : Fin k → Word32) : timesOf (fun j i => ⟪ws j i⟫) = zeroTimes := rfl

/-- **The compression function costs 38656 ANDs of communication.** -/
theorem compress_comm (H : Fin 8 → Word32) (block : Fin 16 → Word32) :
    commOn Bool2.timed ((compressOverBool2 plan).impl .timed (request H block)) = 38656 := by
  rw [request, compress_commOn, timesOf_request, timesOf_request, timeModel_comm]

/-- **The compression function takes 456 rounds.** -/
theorem compress_rounds (H : Fin 8 → Word32) (block : Fin 16 → Word32) :
    readyOn Bool2.timed (.vec 8 W) ((compressOverBool2 plan).impl .timed (request H block)) = 456 := by
  rw [request, compress_readyOn, timesOf_request, timesOf_request, timeModel_ready]

/-- **Correctness and perfect privacy** are the realisation itself: its
output is `compressBlock`, its view is simulated from the (silent) event. -/
noncomputable abbrev theCircuit : Realization SHA256Compress Bool2 := compressOverBool2 plan

theorem theCircuit_real (r : Req SHA256Compress.ops .ideal) :
    dist Bool2.model (theCircuit.impl .ideal r) = (do
      let (y, d) ← SHA256Compress.model.step r
      let s ← theCircuit.Sim ⟨r.op, r.args.blank, (SHA256Compress.ops.cod r.op).blank y, d⟩
      pure (y, s)) :=
  theCircuit.real r (compressOverBool2_pre plan r)

end WeftChals
