import WeftChals.Functionality.Word
import WeftChals.Spec.SHA256

/-!
# The SHA-256 compression function on shared words

Input: a shared chaining value (8 words) and a shared block (16 words);
output: the updated chaining value, `SHA256.compressWords`.  Words
are 32 shared bits, least significant first.
-/
namespace WeftChals
open Weft

/-- Words of bits as numbers. -/
def wordsNat {k : Nat} (ws : Fin k → Word32) : Vector ℕ k := Vector.ofFn fun i => Word32.toNat (ws i)

/-- Numbers as words of bits. -/
def wordsBits {k : Nat} (v : Vector ℕ k) : Fin k → Word32 := fun i => Word32.ofNat v[i]

/-- Shared words as fixed-width integers. -/
def wordsUInt32 {k : Nat} (ws : Fin k → Word32) : Vector UInt32 k :=
  Vector.ofFn fun i => Word32.toUInt32 (ws i)

/-- Fixed-width integers as shared words. -/
def wordsOfUInt32 {k : Nat} (v : Vector UInt32 k) : Fin k → Word32 :=
  fun i => Word32.ofNat v[i].toNat

namespace CompressF
abbrev ops : Interface where
  Op := Unit
  dom _ := [.vec 8 W, .vec 16 W]
  cod _ := .vec 8 W
def eval : Model ops .ideal Id := .silent fun ⟨(), (H, block, ())⟩ =>
  wordsOfUInt32 (SHA256.compressWords (wordsUInt32 H) (wordsUInt32 block))
end CompressF

/-- The compression function of SHA-256, on shared words. -/
abbrev SHA256Compress : Functionality := .ofEval CompressF.ops CompressF.eval
@[simp, weft] theorem SHA256Compress.model_eq : SHA256Compress.model = CompressF.eval.lift PMF :=
  Functionality.ofEval_model _ _

end WeftChals
