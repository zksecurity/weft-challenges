import WeftChals.Circuit.RealRel
import WeftChals.Circuit.Instances
import WeftChals.Functionality.Word
import WeftChals.Sem.Word

/-!
# The word functionalities, realised over `Bool2`

Each realisation runs the word gadget on shares.  Correctness is the
gadget's value lemma; the view is a fixed list (computed by the logging
instance), so the simulator replays it: perfect privacy.
-/
namespace WeftChals
open Weft

/-- Blank operands: what the simulator sees of a word. -/
abbrev blank32 : Fin 32 → Unit := fun _ => ()

/-- The views, computed by the logging instance. -/
def chView : List (Event Bool2.ops) := (chReal (m := Log (Event Bool2.ops)) blank32 blank32 blank32).2
def majView : List (Event Bool2.ops) := (majReal (m := Log (Event Bool2.ops)) blank32 blank32 blank32).2
def csaView : List (Event Bool2.ops) := (csaReal (m := Log (Event Bool2.ops)) blank32 blank32 blank32).2
def addView (net : Net) : List (Event Bool2.ops) := (addReal (m := Log (Event Bool2.ops)) net blank32 blank32).2
def sumView (plan : SumPlan) (ws : List (Fin 32 → Unit)) : List (Event Bool2.ops) :=
  (sumReal (m := Log (Event Bool2.ops)) plan ws).2

/-- Over a hybrid of deterministic functionalities, a deterministic silent
functionality is realised by a program whose output is its model and whose
view is what the simulator replays. -/
theorem real_of_output_view {fs : Hybrid} (hfs : fs.model = fs.eval.lift PMF) {F : Functionality}
    (hF : F.model = F.eval.lift PMF)
    (impl : (r : Req F.ops .ideal) → Prog fs.ops .ideal (Resp F.ops .ideal r.op))
    (Sim : Event F.ops → PMF (List (Event fs.ops))) (r : Req F.ops .ideal)
    (hout : output fs.eval (impl r) = (F.eval.step r).run.1)
    (hview : Sim ⟨r.op, r.args.blank, (F.ops.cod r.op).blank (F.eval.step r).run.1, (F.eval.step r).run.2⟩
      = pure (view fs.eval (impl r))) :
    dist fs.model (impl r) = (do
      let (y, d) ← F.model.step r
      let s ← Sim ⟨r.op, r.args.blank, (F.ops.cod r.op).blank y, d⟩
      pure (y, s)) := by
  rw [hfs, dist_lift, hF, Model.lift_step, hout]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]
  rw [hview]
  simp [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.pure_bind]

/-! ## Outputs and views of the bodies, from the relation lemmas -/

theorem chReal_output (x y z : Wd GF2) : output Bool2.eval (chReal (m := Prog Bool2.ops .ideal) x y z) = Word32.ch x y z := by
  have := Bool2.valRel.chReal x y z
  exact (funext fun i => congrFun this i).trans (chReal_val x y z)

theorem chReal_view (x y z : Wd GF2) : view Bool2.eval (chReal (m := Prog Bool2.ops .ideal) x y z) = chView :=
  (Bool2.viewRel.chReal x y z).2

theorem majReal_output (x y z : Wd GF2) : output Bool2.eval (majReal (m := Prog Bool2.ops .ideal) x y z) = Word32.maj x y z := by
  have := Bool2.valRel.majReal x y z
  exact (funext fun i => congrFun this i).trans (majReal_val x y z)

theorem majReal_view (x y z : Wd GF2) : view Bool2.eval (majReal (m := Prog Bool2.ops .ideal) x y z) = majView :=
  (Bool2.viewRel.majReal x y z).2

theorem Prod.map_wd_id (p : Wd GF2 × Wd GF2) : Prod.map (Wd.map fun x => x) (Wd.map fun x => x) p = p := rfl

theorem csaReal_output (x y z : Wd GF2) :
    output Bool2.eval (csaReal (m := Prog Bool2.ops .ideal) x y z) = (Word32.csaSum x y z, Word32.csaCarry x y z) := by
  have e := Bool2.valRel.csaReal x y z
  rw [Rel.ofOutput] at e
  simp only [Prod.map_wd_id] at e
  rw [e]
  exact csaReal_val x y z

theorem csaReal_view (x y z : Wd GF2) : view Bool2.eval (csaReal (m := Prog Bool2.ops .ideal) x y z) = csaView :=
  (Bool2.viewRel.csaReal x y z).2

theorem addReal_output (net : Net) (x y : Wd GF2) :
    output Bool2.eval (addReal (m := Prog Bool2.ops .ideal) net x y) = Word32.add x y := by
  have := Bool2.valRel.addReal net x y
  exact (funext fun i => congrFun this i).trans (addReal_val net x y)

theorem addReal_view (net : Net) (x y : Wd GF2) :
    view Bool2.eval (addReal (m := Prog Bool2.ops .ideal) net x y) = addView net :=
  (Bool2.viewRel.addReal net x y).2

theorem sumReal_output (plan : SumPlan) (ws : List (Wd GF2)) :
    output Bool2.eval (sumReal (m := Prog Bool2.ops .ideal) plan ws) = Word32.sumList ws := by
  have e := Bool2.valRel.sumReal plan ws
  rw [Rel.ofOutput] at e
  have e' : output Bool2.eval (sumReal (m := Prog Bool2.ops .ideal) plan ws)
      = sumReal (m := Id) plan (ws.map fun w => w) := funext fun i => congrFun e i
  rw [e', List.map_id']
  exact sumReal_val plan ws

theorem sumReal_view (plan : SumPlan) (ws : List (Wd GF2)) :
    view Bool2.eval (sumReal (m := Prog Bool2.ops .ideal) plan ws) = sumView plan (ws.map fun _ => blank32) :=
  (Bool2.viewRel.sumReal plan ws).2

/-! ## The certificates -/

program ch32Real : Realization Ch32 Bool2 where
  impl D r := chReal r.args.1 r.args.2.1 r.args.2.2.1
  Sim _ := pure chView
  real r _ := real_of_output_view Bool2.model_eq Ch32.model_eq (fun r => chReal r.args.1 r.args.2.1 r.args.2.2.1) (fun _ => pure chView) r
    (chReal_output _ _ _) (by rw [chReal_view])

program maj32Real : Realization Maj32 Bool2 where
  impl D r := majReal r.args.1 r.args.2.1 r.args.2.2.1
  Sim _ := pure majView
  real r _ := real_of_output_view Bool2.model_eq Maj32.model_eq (fun r => majReal r.args.1 r.args.2.1 r.args.2.2.1) (fun _ => pure majView) r
    (majReal_output _ _ _) (by rw [majReal_view])

program csa3Real : Realization Csa3 Bool2 where
  impl D r := csaReal r.args.1 r.args.2.1 r.args.2.2.1
  Sim _ := pure csaView
  real r _ := real_of_output_view Bool2.model_eq Csa3.model_eq (fun r => csaReal r.args.1 r.args.2.1 r.args.2.2.1) (fun _ => pure csaView) r
    (csaReal_output _ _ _) (by rw [csaReal_view])

program add32Real : Realization Add32 Bool2 where
  impl D r := addReal r.op r.args.1 r.args.2.1
  Sim e := pure (addView e.op)
  real r _ := real_of_output_view Bool2.model_eq Add32.model_eq (fun r => addReal r.op r.args.1 r.args.2.1) (fun e => pure (addView e.op)) r
    (addReal_output _ _ _) (by rw [addReal_view])

program sum32Real : Realization Sum32 Bool2 where
  impl D r := sumReal r.op r.args.1
  Sim e := pure (sumView e.op e.args.1)
  real r _ := real_of_output_view Bool2.model_eq Sum32.model_eq (fun r => sumReal r.op r.args.1) (fun e => pure (sumView e.op e.args.1)) r
    (sumReal_output _ _) (by rw [sumReal_view]; rfl)

/-- Every component of `Hyb`, realised over `Bool2`. -/
noncomputable def hybOverBool2 : Realizations Hyb Bool2 :=
  .cons (Realization.incl (Lin GF2) Bool2) (.cons ch32Real (.cons maj32Real (.cons csa3Real
    (.cons add32Real (.cons sum32Real .nil)))))

end WeftChals
