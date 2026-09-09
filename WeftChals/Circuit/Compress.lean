import WeftChals.Circuit.WordM
import WeftChals.Spec.SHA256

/-!
# The compression function over the word operations

The structure of the Python generator's `compress`: the message schedule
extended by 48 planned sums, 64 rounds (the early words `h + K[t] + W[t]`
resolved once and shared when the plan says so), and the feed-forward.
Rotations are free re-indexings; shifts need constant `false` bits.
-/
namespace WeftChals
open Weft

universe u
variable {m : Type → Type u} [Monad m] {S : Type} [WordM m S]

namespace Compress

def xorW (x y : Wd S) : m (Wd S) := vecM 32 fun i => bxor (x i) (y i)

def xor3W (x y z : Wd S) : m (Wd S) := do
  let t ← xorW x y
  xorW t z

def rotrW (w : Wd S) (n : Nat) : Wd S := fun i => w ⟨(i.val + n) % 32, Nat.mod_lt _ (by decide)⟩

def shrW (w : Wd S) (n : Nat) : m (Wd S) := vecM 32 fun i =>
  if h : i.val + n < 32 then pure (w ⟨i.val + n, h⟩) else bconst false

/-- A public constant word, as shares. -/
def constW (n : Nat) : m (Wd S) := vecM 32 fun i => bconst (n.testBit i)

def sigma0 (x : Wd S) : m (Wd S) := do
  let s ← shrW x 3
  xor3W (rotrW x 7) (rotrW x 18) s
def sigma1 (x : Wd S) : m (Wd S) := do
  let s ← shrW x 10
  xor3W (rotrW x 17) (rotrW x 19) s
def bigSigma0 (x : Wd S) : m (Wd S) := xor3W (rotrW x 2) (rotrW x 13) (rotrW x 22)
def bigSigma1 (x : Wd S) : m (Wd S) := xor3W (rotrW x 6) (rotrW x 11) (rotrW x 25)

/-- Extend the schedule by one word. -/
def scheduleStep (zero : Wd S) (W : List (Wd S)) (p : SumPlan) : m (List (Wd S)) := do
  let t := W.length
  let s1 ← sigma1 (W.getD (t - 2) zero)
  let s0 ← sigma0 (W.getD (t - 15) zero)
  let w ← WordM.sum p [s1, W.getD (t - 7) zero, s0, W.getD (t - 16) zero]
  pure (W ++ [w])

/-- The working state `a, b, c, d, e, f, g, h`. -/
structure State (S : Type) where
  a : Wd S
  b : Wd S
  c : Wd S
  d : Wd S
  e : Wd S
  f : Wd S
  g : Wd S
  h : Wd S

/-- One round: `k` is the round constant, `w` the schedule word. -/
def round (st : State S) (arg : Nat × Wd S × RoundPlan) : m (State S) := do
  let k ← constW arg.1
  let w := arg.2.1
  let rp := arg.2.2
  let s1 ← bigSigma1 st.e
  let ch ← WordM.ch st.e st.f st.g
  let s0 ← bigSigma0 st.a
  let mj ← WordM.maj st.a st.b st.c
  match rp.base with
  | some pb => do
    let base ← WordM.sum pb [st.h, k, w]
    let na ← WordM.sum rp.newA [base, s1, ch, s0, mj]
    let ne ← WordM.sum rp.newE [base, st.d, s1, ch]
    pure ⟨na, st.a, st.b, st.c, ne, st.e, st.f, st.g⟩
  | none => do
    let bc ← WordM.csa st.h k w
    let na ← WordM.sum rp.newA [bc.1, bc.2, s1, ch, s0, mj]
    let ne ← WordM.sum rp.newE [bc.1, bc.2, st.d, s1, ch]
    pure ⟨na, st.a, st.b, st.c, ne, st.e, st.f, st.g⟩

/-- The round constants, as a list (the specification's vector, without
the array indexing the certificate checker rejects). -/
def kList : List Nat := [
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

theorem kList_eq : kList = (List.range 64).map fun t => (Wychelean.Hashes.SHA256.K[t]!).toNat := by decide

/-- A plan with no structure: every sum falls back to the fixed order. -/
def dfltSum : SumPlan := ⟨[], ⟨31, []⟩⟩

/-- Exactly 48 schedule plans and 64 round plans, whatever the plan holds. -/
def schedulePlans (plan : BlockPlan) : List SumPlan := (plan.schedule ++ List.replicate 48 dfltSum).take 48
def roundPlans (plan : BlockPlan) : List RoundPlan := (plan.rounds ++ List.replicate 64 (⟨none, dfltSum, dfltSum⟩ : RoundPlan)).take 64

/-- The compression function: schedule, rounds, feed-forward. -/
def compress (plan : BlockPlan) (H : Fin 8 → Wd S) (block : Fin 16 → Wd S) : m (Fin 8 → Wd S) := do
  let zero ← constW 0
  let W ← foldM (scheduleStep zero) (finList 16 block) (schedulePlans plan)
  let st0 : State S := ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩
  let st ← foldM round st0 (List.zip kList (List.zip W (roundPlans plan)))
  let outs : Fin 8 → Wd S := consFin st.a (consFin st.b (consFin st.c (consFin st.d
    (consFin st.e (consFin st.f (consFin st.g (consFin st.h fun i => i.elim0)))))))
  vecM 8 fun i => WordM.add (plan.final.getD i ⟨31, []⟩) (H i) (outs i)

end Compress

end WeftChals
