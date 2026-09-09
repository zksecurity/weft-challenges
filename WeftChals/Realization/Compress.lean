import WeftChals.Circuit.HybInst
import WeftChals.Realization.Word
import WeftChals.Sem.Compress

/-!
# The compression function, realised

Over `Hyb`, the program is the compression circuit with the word
operations as black boxes; its output is Wychelean’s `compress` and its view is
a fixed list, so the simulator replays it.  Composing with the word
realisations gives the compression function over Boolean circuits, with
correctness and perfect privacy by weft's composition theorem.
-/
namespace WeftChals
open Weft

/-- Blank words: what the adversary sees of the inputs. -/
abbrev blankWords {k : Nat} : Fin k → Fin 32 → Unit := fun _ _ => ()

/-- The view of the compression program over `Hyb`, computed by the logging instance. -/
def compressView (plan : BlockPlan) : List (Event Hyb.ops) :=
  (Compress.compress (m := Log (Event Hyb.ops)) plan blankWords blankWords).2

theorem compress_output (plan : BlockPlan) (H : Fin 8 → Word32) (block : Fin 16 → Word32) :
    output Hyb.eval (Compress.compress (m := Prog Hyb.ops .ideal) plan H block)
      = wordsOfUInt32 (SHA256.compressWords (wordsUInt32 H) (wordsUInt32 block)) := by
  have e : output Hyb.eval (Compress.compress (m := Prog Hyb.ops .ideal) plan H block)
      = Compress.compress (m := Id) plan H block := Hyb.valRel.compress plan H block
  rw [e]
  exact Compress.compress_val plan H block

theorem compress_view (plan : BlockPlan) (H : Fin 8 → Word32) (block : Fin 16 → Word32) :
    view Hyb.eval (Compress.compress (m := Prog Hyb.ops .ideal) plan H block) = compressView plan :=
  (Hyb.viewRel.compress plan H block).2

/-- The compression function over the word functionalities. -/
program compressReal (plan : BlockPlan) : Realization SHA256Compress Hyb where
  impl D r := Compress.compress plan r.args.1 r.args.2.1
  Sim _ := pure (compressView plan)
  real r _ := real_of_output_view Hyb.model_eq SHA256Compress.model_eq
    (fun r => Compress.compress plan r.args.1 r.args.2.1) (fun _ => pure (compressView plan)) r
    (compress_output plan _ _) (by rw [compress_view])

/-- **The compression function over Boolean circuits**: the word
functionalities inlined.  Correct and perfectly private by composition. -/
noncomputable def compressOverBool2 (plan : BlockPlan) : Realization SHA256Compress Bool2 :=
  (compressReal plan).comp hybOverBool2

/-- Its precondition is trivial: every request is valid. -/
theorem compressOverBool2_pre (plan : BlockPlan) (r : Req SHA256Compress.ops .ideal) :
    (compressOverBool2 plan).Pre r :=
  ⟨trivial, Valid.of_forall _ (fun r => by
    obtain ⟨⟨⟨_ | _ | _ | _ | _ | _ | n, h⟩, o⟩, a⟩ := r <;> trivial) _⟩

end WeftChals
