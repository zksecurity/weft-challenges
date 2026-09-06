import WeftChals.Circuit.Sum

/-!
# The word gadgets on shares

Each word functionality is realised by a Boolean gadget on words of
shares: wrap the operand bits as `Bit.var`, run the gadget, share the
result (a constant bit costs one free request).  The same functions,
instantiated in the counting writer, are the timing model of the word
operations at the hybrid level.
-/
namespace WeftChals

universe u
variable {m : Type → Type u} [Monad m] {S : Type} [BitM m S]

/-- A word of shares. -/
abbrev Wd (S : Type) := Fin 32 → S

def chReal (x y z : Wd S) : m (Wd S) := do
  let w ← Word.ch (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)
  w.materialize

def majReal (x y z : Wd S) : m (Wd S) := do
  let w ← Word.maj (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)
  w.materialize

def csaReal (x y z : Wd S) : m (Wd S × Wd S) := do
  let r ← Word.csa3 (Word.ofShares x) (Word.ofShares y) (Word.ofShares z)
  let s ← r.1.materialize
  let c ← r.2.materialize
  pure (s, c)

def addReal (net : Net) (x y : Wd S) : m (Wd S) := do
  let w ← Adder.add net (Word.ofShares x) (Word.ofShares y)
  w.materialize

def sumReal (plan : SumPlan) (ws : List (Wd S)) : m (Wd S) := do
  let w ← Sum32.sum plan (ws.map Word.ofShares)
  w.materialize

end WeftChals
