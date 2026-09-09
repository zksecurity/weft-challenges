import Mathlib.Data.Nat.Bitwise

/-!
# Natural-number helpers for the shared-bit word model
-/

def add32 (a b : ℕ) : ℕ := (a + b) % 2^32
