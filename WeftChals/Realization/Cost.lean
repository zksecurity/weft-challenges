import WeftChals.Realization.Compress

/-!
# Round complexity and communication

The cost of the composed program (the compression function inlined into
Boolean circuits) is the cost of the hybrid program with every word
operation instantiated by its realisation (`Realizations.sched_timed`);
that program relates to the pure timing model `timeModel`, the
compression program in the counting writer on ready times; and the
model's numbers are decided by the kernel.
-/
namespace WeftChals
open Weft

/-- The cost instantiation of `Hyb`: every word operation runs its realisation over `Bool2`. -/
noncomputable abbrev HybT : Model Hyb.ops .timed Sched := hybOverBool2.timed Bool2.timed

/-- The pure timing model: the compression program on ready times, counting ANDs. -/
def timeModel (plan : BlockPlan) (H : Fin 8 → Wd Nat) (block : Fin 16 → Wd Nat) : Count (Fin 8 → Wd Nat) :=
  Compress.compress (m := Count) plan H block

/-- When every output bit is ready. -/
def maxTime (o : Fin 8 → Wd Nat) : Nat :=
  (List.finRange 8).foldr (fun j m => max ((List.finRange 32).foldr (fun i m => max (o j i) m) 0) m) 0

/-! ## The timing laws of `Hyb`, from those of `Bool2` -/

/-- A request to component `i` under the realisations' timed model relates
to whatever the component's implementation relates to
(`Realizations.run_opAt`, once, on abstract terms). -/
theorem Rel.ofTimed_opAt {fs gs : Hybrid} (g : Realizations fs gs) (T : Model gs.ops .timed Sched)
    (i : Fin fs.length) (r : Req (fs.get i).ops .timed) {β : Type}
    {f : Resp (fs.get i).ops .timed r.op → β} {y : Count β}
    (h : (Rel.ofTimed T).R f ((g.get i).impl .timed r) y) :
    (Rel.ofTimed (g.timed T)).R f (Prog.opAt fs i r) y := by
  intro s hs
  show f (StateT.run (run (g.timed T) CostModel.unit (Prog.opAt fs i r)) s).1.1 = y.1 ∧ _
  rw [Realizations.run_opAt]
  exact h s hs

namespace Hyb

/-- The wire map: a share's ready time. -/
abbrev tm : Domain.timed.share GF2 → Nat := fun x => x.time

/-! The timing laws of `Hyb`: a request to a component runs that
component's realisation over `Bool2`, whose timing is the Boolean-level
law; the request's position form and the component's body are
definitional. -/

theorem xor_law (a b : Timed GF2) :
    (Rel.ofTimed HybT).R tm (bxor (m := Prog Hyb.ops .timed) a b) (bxor (m := Count) (tm a) (tm b)) :=
  Rel.ofTimed_opAt hybOverBool2 Bool2.timed ⟨0, by decide⟩ ⟨.add, (a, b, ())⟩ (Bool2.timeRel.pxor a b)

theorem const_law (b : Bool) :
    (Rel.ofTimed HybT).R tm (bconst (m := Prog Hyb.ops .timed) b) (bconst (m := Count) b) :=
  Rel.ofTimed_opAt hybOverBool2 Bool2.timed ⟨0, by decide⟩ ⟨.const, (Timed.now (GF2.ofBool b), ())⟩
    (Bool2.timeRel.pconst b)

theorem ch_law (x y z : Wd (Timed GF2)) :
    (Rel.ofTimed HybT).R (Wd.map tm) (WordM.ch (m := Prog Hyb.ops .timed) x y z)
      (WordM.ch (m := Count) (Wd.map tm x) (Wd.map tm y) (Wd.map tm z)) :=
  Rel.ofTimed_opAt hybOverBool2 Bool2.timed ⟨1, by decide⟩ ⟨(), (x, y, z, ())⟩ (Bool2.timeRel.chReal x y z)

theorem maj_law (x y z : Wd (Timed GF2)) :
    (Rel.ofTimed HybT).R (Wd.map tm) (WordM.maj (m := Prog Hyb.ops .timed) x y z)
      (WordM.maj (m := Count) (Wd.map tm x) (Wd.map tm y) (Wd.map tm z)) :=
  Rel.ofTimed_opAt hybOverBool2 Bool2.timed ⟨2, by decide⟩ ⟨(), (x, y, z, ())⟩ (Bool2.timeRel.majReal x y z)

theorem csa_law (x y z : Wd (Timed GF2)) :
    (Rel.ofTimed HybT).R (Prod.map (Wd.map tm) (Wd.map tm)) (WordM.csa (m := Prog Hyb.ops .timed) x y z)
      (WordM.csa (m := Count) (Wd.map tm x) (Wd.map tm y) (Wd.map tm z)) :=
  Rel.ofTimed_opAt hybOverBool2 Bool2.timed ⟨3, by decide⟩ ⟨(), (x, y, z, ())⟩ (Bool2.timeRel.csaReal x y z)

theorem add_law (net : Net) (x y : Wd (Timed GF2)) :
    (Rel.ofTimed HybT).R (Wd.map tm) (WordM.add (m := Prog Hyb.ops .timed) net x y)
      (WordM.add (m := Count) net (Wd.map tm x) (Wd.map tm y)) :=
  Rel.ofTimed_opAt hybOverBool2 Bool2.timed ⟨4, by decide⟩ ⟨net, (x, y, ())⟩ (Bool2.timeRel.addReal net x y)

theorem sum_law (plan : SumPlan) (ws : List (Wd (Timed GF2))) :
    (Rel.ofTimed HybT).R (Wd.map tm) (WordM.sum (m := Prog Hyb.ops .timed) plan ws)
      (WordM.sum (m := Count) plan (ws.map (Wd.map tm))) :=
  Rel.ofTimed_opAt hybOverBool2 Bool2.timed ⟨5, by decide⟩ ⟨plan, (ws, ())⟩ (Bool2.timeRel.sumReal plan ws)

theorem timeRel : WordRel (Rel.ofTimed HybT) tm :=
  { pxor := xor_law, pconst := const_law, pch := ch_law, pmaj := maj_law, pcsa := csa_law, padd := add_law,
    psum := sum_law }

end Hyb

/-- Ready times of the inputs. -/
def timesOf {k : Nat} (ws : Fin k → Wd (Timed GF2)) : Fin k → Wd Nat := fun j => Wd.map Timed.time (ws j)

/-- The composed program's scheduled run is the timing model's. -/
theorem compress_sched (plan : BlockPlan) (H : Fin 8 → Wd (Timed GF2)) (block : Fin 16 → Wd (Timed GF2)) :
    (fun (o : Fin 8 → Wd (Timed GF2)) => timesOf o)
        (Sched.run Bool2.timed ((compressOverBool2 plan).impl .timed ⟨(), (H, block, ())⟩)).1
      = (timeModel plan (timesOf H) (timesOf block)).1 ∧
    (Sched.run Bool2.timed ((compressOverBool2 plan).impl .timed ⟨(), (H, block, ())⟩)).2
      = ⟨0, (timeModel plan (timesOf H) (timesOf block)).2⟩ := by
  have e : (compressOverBool2 plan).impl .timed ⟨(), (H, block, ())⟩
      = Prog.handle (hybOverBool2.impl .timed) ((compressReal plan).impl .timed ⟨(), (H, block, ())⟩) := rfl
  have e0 : (compressReal plan).impl .timed ⟨(), (H, block, ())⟩
      = Compress.compress (m := Prog Hyb.ops .timed) plan H block := rfl
  rw [e, ← Realizations.sched_timed, e0]
  simp only [Sched.run, Id.run]
  have key := Hyb.timeRel.compress plan H block {} rfl
  refine ⟨key.1, ?_⟩
  rw [key.2]
  simp only [Nat.zero_add]
  rfl

/-- **Communication**: the AND count of the timing model. -/
theorem compress_commOn (plan : BlockPlan) (H : Fin 8 → Wd (Timed GF2)) (block : Fin 16 → Wd (Timed GF2)) :
    commOn Bool2.timed ((compressOverBool2 plan).impl .timed ⟨(), (H, block, ())⟩)
      = (timeModel plan (timesOf H) (timesOf block)).2 := by
  simp only [commOn]
  rw [(compress_sched plan H block).2]

/-- **Round complexity**: when the output is ready, by the timing model. -/
theorem compress_readyOn (plan : BlockPlan) (H : Fin 8 → Wd (Timed GF2)) (block : Fin 16 → Wd (Timed GF2)) :
    readyOn Bool2.timed (.vec 8 W) ((compressOverBool2 plan).impl .timed ⟨(), (H, block, ())⟩)
      = maxTime (timeModel plan (timesOf H) (timesOf block)).1 := by
  obtain ⟨h1, h2⟩ := compress_sched plan H block
  simp only [readyOn, h2, Nat.max_zero]
  rw [← h1]
  rfl

end WeftChals
