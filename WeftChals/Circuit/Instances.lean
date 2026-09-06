import Weft
import WeftChals.Circuit.Rel

/-!
# The instances of a Boolean gadget, and how they relate

* `progBitM`: the weft program over any hybrid offering `Lin GF2` and `Mult GF2`.
* `valBitM`: values in `GF2`, at `Id`.
* `timeBitM`: ready times in `ℕ` and the AND count, in the counting writer.
* `viewBitM`: the events of `Bool2`, in the logging writer; wires are `Unit`.

`Rel.ofOutput`, `Rel.ofView` and `Rel.ofTimed` relate the program to the
three pure instances through weft's interpreter; `Bool2.valRel`,
`Bool2.viewRel` and `Bool2.timeRel` are the primitive laws for `Bool2`.
-/
namespace WeftChals
open Weft

instance progLinM {fs : Hybrid} {D : Domain} [Has (Lin GF2) fs] : LinM (Prog fs.ops D) (D.share GF2) where
  bxor := add
  bconst b := Weft.const (pure (GF2.ofBool b))

instance progBitM {fs : Hybrid} {D : Domain} [Has (Lin GF2) fs] [Has (Mult GF2) fs] :
    BitM (Prog fs.ops D) (D.share GF2) where
  band := mul

instance valLinM : LinM Id GF2 where
  bxor a b := pure (a + b)
  bconst b := pure (GF2.ofBool b)

instance valBitM : BitM Id GF2 where
  band a b := pure (a * b)

/-- Xor is ready when both inputs are; an AND one round later, and it counts. -/
instance timeLinM : LinM Count Nat where
  bxor a b := (max a b, 0)
  bconst _ := (0, 0)

instance timeBitM : BitM Count Nat where
  band a b := (max a b + 1, 1)

instance viewLinM : LinM (Log (Event Bool2.ops)) Unit where
  bxor _ _ := ((), [⟨Bool2.lin .add, ((), (), ()), (), ()⟩])
  bconst b := ((), [⟨Bool2.lin .const, (GF2.ofBool b, ()), (), ()⟩])

instance viewBitM : BitM (Log (Event Bool2.ops)) Unit where
  band _ _ := ((), [⟨Bool2.mult, ((), (), ()), (), ()⟩])

/-! ## From the program to the pure instances -/

/-- Outputs: `g (output c) = y`. -/
def Rel.ofOutput {ι : Interface} (M : Model ι .ideal Id) : Rel (Prog ι .ideal) Id where
  R g x y := g (output M x) = y
  pure _ _ := rfl
  bind {_ _ _ _ g h x y k l} hx hk := by
    show h (output M (Prog.bind x k)) = l y
    rw [output_bind, ← hx]
    exact hk _

/-- Outputs and views: `g (output c) = y.1` and `view c = y.2`. -/
def Rel.ofView {ι : Interface} (M : Model ι .ideal Id) : Rel (Prog ι .ideal) (Log (Event ι)) where
  R g x y := g (output M x) = y.1 ∧ view M x = y.2
  pure _ _ := ⟨rfl, rfl⟩
  bind {_ _ _ _ g h x y k l} hx hk := by
    obtain ⟨h1, h2⟩ := hx
    obtain ⟨h3, h4⟩ := hk (output M x)
    rw [h1] at h3 h4
    refine ⟨?_, ?_⟩
    · show h (output M (Prog.bind x k)) = (l y.1).1
      rw [output_bind]
      exact h3
    · show view M (Prog.bind x k) = y.2 ++ (l y.1).2
      rw [view_bind, h2, h4]

/-- Times and communication: from any state at clock `0`, the run's output
maps to `y.1` and it pays `y.2`, leaving the clock at `0`. -/
def Rel.ofTimed {ι : Interface} (M : Model ι .timed Sched) : Rel (Prog ι .timed) Count where
  R g x y := ∀ s : Clock, s.clock = 0 →
    g (StateT.run (run M CostModel.unit x) s).1.1 = y.1 ∧
      (StateT.run (run M CostModel.unit x) s).2 = ⟨0, s.comm + y.2⟩
  pure g a s hs := by
    refine ⟨rfl, ?_⟩
    show s = ⟨0, s.comm + 0⟩
    cases s; simp_all
  bind {_ _ _ _ g h x y k l} hx hk s hs := by
    obtain ⟨h1, h2⟩ := hx s hs
    obtain ⟨h3, h4⟩ := hk (StateT.run (run M CostModel.unit x) s).1.1 ⟨0, s.comm + y.2⟩ rfl
    rw [h1] at h3 h4
    have e : StateT.run (run M CostModel.unit (Prog.bind x k)) s =
        (((StateT.run (run M CostModel.unit (k (StateT.run (run M CostModel.unit x) s).1.1))
            (StateT.run (run M CostModel.unit x) s).2).1.1,
          Trace.seq (StateT.run (run M CostModel.unit x) s).1.2
            (StateT.run (run M CostModel.unit (k (StateT.run (run M CostModel.unit x) s).1.1))
              (StateT.run (run M CostModel.unit x) s).2).1.2),
         (StateT.run (run M CostModel.unit (k (StateT.run (run M CostModel.unit x) s).1.1))
            (StateT.run (run M CostModel.unit x) s).2).2) := by
      rw [run_bind]
      rfl
    show h (StateT.run (run M CostModel.unit (x >>= k)) s).1.1 = (l y.1).1 ∧
      (StateT.run (run M CostModel.unit (x >>= k)) s).2 = ⟨0, s.comm + (y.2 + (l y.1).2)⟩
    rw [Prog.bind_eq, e, h2]
    exact ⟨h3, by rw [h4]; simp [Nat.add_assoc]⟩

/-! ## The primitive laws for `Bool2` -/

namespace Bool2

theorem valRel : BitRel (Rel.ofOutput Bool2.eval) (fun x : Domain.ideal.share GF2 => (x : GF2)) where
  pxor _ _ := rfl
  pand _ _ := rfl
  pconst _ := rfl

theorem viewRel : BitRel (Rel.ofView Bool2.eval) (fun _ : Domain.ideal.share GF2 => ()) where
  pxor _ _ := ⟨rfl, rfl⟩
  pand _ _ := ⟨rfl, rfl⟩
  pconst _ := ⟨rfl, rfl⟩

theorem timeRel : BitRel (Rel.ofTimed Bool2.timed) (fun x : Domain.timed.share GF2 => x.time) where
  pxor a b s hs := by
    refine ⟨?_, ?_⟩
    · show max (max a.time (max b.time 0)) s.clock + 0 = max a.time b.time
      rw [hs]; omega
    · show s = ⟨0, s.comm + 0⟩
      cases s; simp_all
  pand a b s hs := by
    refine ⟨?_, ?_⟩
    · show max (max a.time (max b.time 0)) s.clock + 1 = max a.time b.time + 1
      rw [hs]; omega
    · show ({ s with comm := s.comm + 1 } : Clock) = ⟨0, s.comm + 1⟩
      cases s; simp_all
  pconst b s hs := by
    refine ⟨?_, ?_⟩
    · show max (max 0 0) s.clock + 0 = 0
      rw [hs]; rfl
    · show s = ⟨0, s.comm + 0⟩
      cases s; simp_all

end Bool2

end WeftChals
