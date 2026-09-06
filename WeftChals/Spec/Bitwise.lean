import Mathlib.Data.Nat.Bitwise

/-!
# 32-bit word helpers used by the SHA-256 specification

Copied from `Clean.Utils.Bitwise` (the `clean` package golf's spec imports).
-/

def add32 (a b : ℕ) : ℕ := (a + b) % 2^32

def rotRight32 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 32
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(32-offset)) + high
