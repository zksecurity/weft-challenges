import WeftChals.Realization.Compress
import WeftChals.Plans.Compression

/-!
# Known-answer tests of the circuits

Evaluated by compiled code (`native_decide`), outside the certified
development.  The Boolean word gadgets are run by weft's interpreter on
concrete words (each a few hundred requests); the whole compression
circuit (the word gadgets on the bits' values, on the exported plan and on
the empty plan) is run in a strict data monad on the standard IV and the
padded block of `"abc"`.  Correctness holds for every plan, so the empty
plan (fallback structure) and a few hand-written networks are exercised
too.

The circuit is not evaluated at `Id`: the compiler eta-expands
function-typed words there and recomputes every word per bit, which is
exponential in the number of rounds.
-/
namespace WeftChals.Tests
open Weft WeftChals

/-- A few words. -/
def w1 : Word32 := Word32.ofNat 0x6a09e667
def w2 : Word32 := Word32.ofNat 0xbb67ae85
def w3 : Word32 := Word32.ofNat 0x3c6ef372
def w4 : Word32 := Word32.ofNat 0xffffffff
def w5 : Word32 := Word32.ofNat 0x80000001

/-- A Sklansky-like network on 31 elements, as productions. -/
def sklansky : Net := ⟨31, Id.run do
  let mut prods : List Nat := []
  for stage in [0, 1, 2, 3, 4] do
    let half := 1 <<< stage
    let block := half <<< 1
    let mut base := 0
    while base < 31 do
      let pivot := base + half - 1
      if pivot < 31 then
        for i in [base + half : min (base + block) 31] do
          prods := prods ++ [32768 + base * 1024 + i * 32 + pivot]
          if stage < 4 then prods := prods ++ [base * 1024 + i * 32 + pivot]
      base := base + block
  pure prods⟩

def ripple31 : Net := ⟨31, (List.range' 1 30).map fun k => 32768 + k * 32 + (k - 1)⟩
def ripple30 : Net := ⟨30, (List.range' 1 29).map fun k => 32768 + k * 32 + (k - 1)⟩

/-! ## The word gadgets, by weft's interpreter -/

/-- Run a Boolean gadget body by weft's interpreter and read the word. -/
def runB (p : Prog Bool2.ops .ideal Word32) : Nat := Word32.toNat (output Bool2.eval p)

example : runB (chReal w1 w2 w3) = Word32.toNat (Word32.ch w1 w2 w3) := by native_decide
example : runB (majReal w1 w2 w3) = Word32.toNat (Word32.maj w1 w2 w3) := by native_decide
example : Word32.toNat (output Bool2.eval (csaReal w4 w5 w1)).1 = Word32.toNat (Word32.csaSum w4 w5 w1) := by
  native_decide
example : Word32.toNat (output Bool2.eval (csaReal w4 w5 w1)).2 = Word32.toNat (Word32.csaCarry w4 w5 w1) := by
  native_decide
example : runB (addReal ripple31 w4 w5) = add32 (Word32.toNat w4) (Word32.toNat w5) := by native_decide
example : runB (addReal sklansky w1 w2) = add32 (Word32.toNat w1) (Word32.toNat w2) := by native_decide
example : runB (addReal sklansky w4 w5) = add32 (Word32.toNat w4) (Word32.toNat w5) := by native_decide
example : runB (addReal ⟨31, [1, 2, 3]⟩ w4 w5) = add32 (Word32.toNat w4) (Word32.toNat w5) := by native_decide
example : runB (sumReal ⟨[10, 10], ripple30⟩ [w1, w2, w3, w4]) = (0x6a09e667 + 0xbb67ae85 + 0x3c6ef372 + 0xffffffff) % 2 ^ 32 := by
  native_decide
example : runB (sumReal ⟨[10, 10, 10], sklansky⟩ [w1, w2, w3, w4, w5]) =
    (0x6a09e667 + 0xbb67ae85 + 0x3c6ef372 + 0xffffffff + 0x80000001) % 2 ^ 32 := by
  native_decide
example : runB (sumReal ⟨[], ⟨30, []⟩⟩ [w1, w2, w3, w4, w5]) =
    (0x6a09e667 + 0xbb67ae85 + 0x3c6ef372 + 0xffffffff + 0x80000001) % 2 ^ 32 := by
  native_decide

/-! ## The whole circuit, on the bits' values -/

instance : LinM Option GF2 where
  bxor a b := some (a + b)
  bconst b := some (GF2.ofBool b)

instance : BitM Option GF2 where
  band a b := some (a * b)

/-- The word operations by their Boolean gadgets: the compression circuit. -/
instance : WordM Option GF2 where
  ch := chReal
  maj := majReal
  csa := csaReal
  add := addReal
  sum := sumReal

def iv : Fin 8 → Word32 := wordsOfUInt32 (SHA256.stateWords Wychelean.Hashes.SHA256.H0)

/-- The padded block of `"abc"`. -/
def abcBlock : Fin 16 → Word32 := fun j =>
  Word32.ofNat (if j.val = 0 then 0x61626380 else if j.val = 15 then 0x18 else 0)

def abcDigest : Vector Nat 8 :=
  #v[0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad]

/-- The exported circuit computes `sha256("abc")`. -/
example : (Compress.compress (m := Option) Plans.Compression.plan iv abcBlock).map wordsNat = some abcDigest := by
  native_decide

/-- So does the fallback structure of the empty plan. -/
example : (Compress.compress (m := Option) ⟨[], [], []⟩ iv abcBlock).map wordsNat = some abcDigest := by
  native_decide

/-- A non-IV state and a block with all bit positions exercised. -/
private def arbitraryState : Fin 8 → Word32 := fun i =>
  Word32.ofNat (0xfedcba98 + i.val * 0x1020304)

private def arbitraryBlock : Fin 16 → Word32 := fun i =>
  Word32.ofNat (0x89abcdef + i.val * 0x1234567)

example : (Compress.compress (m := Option) Plans.Compression.plan arbitraryState arbitraryBlock).map wordsUInt32 =
    some (SHA256.compressWords (wordsUInt32 arbitraryState) (wordsUInt32 arbitraryBlock)) := by
  native_decide

example : (Compress.compress (m := Option) ⟨[], [], []⟩ arbitraryState arbitraryBlock).map wordsUInt32 =
    some (SHA256.compressWords (wordsUInt32 arbitraryState) (wordsUInt32 arbitraryBlock)) := by
  native_decide

end WeftChals.Tests
