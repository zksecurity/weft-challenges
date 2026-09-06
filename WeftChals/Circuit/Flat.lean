import WeftChals.Circuit.Sum
import WeftChals.Spec.SHA256

/-!
# The compression function, flat

The whole compression built directly from the bit-level gadgets, generic
in the monad: the inlined circuit.  Used to benchmark evaluation.
-/
namespace WeftChals

universe u
variable {m : Type → Type u} [Monad m] {S : Type} [BitM m S]

namespace Flat

def sigma0 (x : Word S) : m (Word S) := Word.xor3 (x.rotr 7) (x.rotr 18) (x.shr 3)
def sigma1 (x : Word S) : m (Word S) := Word.xor3 (x.rotr 17) (x.rotr 19) (x.shr 10)
def bigSigma0 (x : Word S) : m (Word S) := Word.xor3 (x.rotr 2) (x.rotr 13) (x.rotr 22)
def bigSigma1 (x : Word S) : m (Word S) := Word.xor3 (x.rotr 6) (x.rotr 11) (x.rotr 25)

/-- Extend the schedule by one word. -/
def scheduleStep (W : List (Word S)) (p : SumPlan) : m (List (Word S)) := do
  let t := W.length
  let z : Word S := Word.const 0
  let s1 ← sigma1 (W.getD (t - 2) z)
  let s0 ← sigma0 (W.getD (t - 15) z)
  let w ← Sum32.sum p [s1, W.getD (t - 7) z, s0, W.getD (t - 16) z]
  pure (W ++ [w])

structure State (S : Type) where
  a : Word S
  b : Word S
  c : Word S
  d : Word S
  e : Word S
  f : Word S
  g : Word S
  h : Word S

def round (st : State S) (arg : Word S × Word S × RoundPlan) : m (State S) := do
  let k := arg.1
  let w := arg.2.1
  let rp := arg.2.2
  let s1 ← bigSigma1 st.e
  let ch ← Word.ch st.e st.f st.g
  let s0 ← bigSigma0 st.a
  let mj ← Word.maj st.a st.b st.c
  match rp.base with
  | some pb => do
    let base ← Sum32.sum pb [st.h, k, w]
    let na ← Sum32.sum rp.newA [base, s1, ch, s0, mj]
    let ne ← Sum32.sum rp.newE [base, st.d, s1, ch]
    pure ⟨na, st.a, st.b, st.c, ne, st.e, st.f, st.g⟩
  | none => do
    let bc ← Word.csa3 st.h k w
    let na ← Sum32.sum rp.newA [bc.1, bc.2, s1, ch, s0, mj]
    let ne ← Sum32.sum rp.newE [bc.1, bc.2, st.d, s1, ch]
    pure ⟨na, st.a, st.b, st.c, ne, st.e, st.f, st.g⟩

def kWords : List (Word S) := (List.range 64).map fun t => Word.const (Specs.SHA256.K[t]!).toNat

def compress (plan : BlockPlan) (H : List (Word S)) (block : List (Word S)) : m (List (Word S)) := do
  let W ← foldM scheduleStep block plan.schedule
  let z : Word S := Word.const 0
  let st0 : State S := ⟨H.getD 0 z, H.getD 1 z, H.getD 2 z, H.getD 3 z, H.getD 4 z, H.getD 5 z, H.getD 6 z, H.getD 7 z⟩
  let args := List.zip kWords (List.zip W plan.rounds)
  let st ← foldM round st0 args
  let outs := [st.a, st.b, st.c, st.d, st.e, st.f, st.g, st.h]
  listM (fun (p : (Word S × Word S) × Net) => Adder.add p.2 p.1.1 p.1.2) (List.zip (List.zip H outs) plan.final)

end Flat

/-! ## A synthetic plan: ripple adders, canonical compression order -/
namespace Synthetic

def rippleNet (n : Nat) : Net := ⟨n, (List.range' 1 (n - 1)).map fun k => 32768 + k * 32 + (k - 1)⟩
def canon (k : Nat) (n : Nat) : SumPlan := ⟨List.replicate (k - 2) 10, rippleNet n⟩
def plan : BlockPlan :=
  ⟨List.replicate 48 (canon 4 30),
   List.replicate 64 ⟨some (canon 3 30), canon 5 30, canon 4 30⟩,
   List.replicate 8 (rippleNet 31)⟩

end Synthetic

end WeftChals
