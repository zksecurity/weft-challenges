import Mathlib.Data.Fin.Tuple.Basic

/-!
# Bit-level circuits, generically

A gadget is written once, over any monad `m` that offers the three
primitives of a Boolean circuit on wires `S`: xor, and, and a public
constant as a wire.  Instantiated at weft's free monad it is the program
whose cost and privacy are certified; at `Id` on `GF2` it is the pure
function the correctness proof reasons about; at a writer on `ℕ` it is
the pure timing model the kernel evaluates for depth and AND count.

Wires carry public constants (`Bit.const`) beside shares (`Bit.var`), and
the folding layer never issues a request whose result is known: this is
exactly the constant folding of the Python generator, without its
wire-identity rules (two shares cannot be compared).
-/
namespace WeftChals

universe u

/-- The linear primitives of a Boolean circuit over wires `S`, in `m`. -/
class LinM (m : Type → Type u) (S : outParam Type) where
  bxor : S → S → m S
  bconst : Bool → m S

/-- The primitives of a Boolean circuit: the linear ones and `and`. -/
class BitM (m : Type → Type u) (S : outParam Type) extends LinM m S where
  band : S → S → m S

export LinM (bxor bconst)
export BitM (band)

/-- A wire: a public constant or a share. -/
inductive Bit (S : Type) where
  | const (b : Bool)
  | var (s : S)
  deriving Repr

namespace Bit
variable {S T : Type}

def map (f : S → T) : Bit S → Bit T
  | const b => const b
  | var s => var (f s)

@[simp] theorem map_const (f : S → T) (b : Bool) : map f (const b) = const b := rfl
@[simp] theorem map_var (f : S → T) (s : S) : map f (var s) = var (f s) := rfl
@[simp] theorem map_id (x : Bit S) : map id x = x := by cases x <;> rfl
theorem map_map {U : Type} (f : S → T) (g : T → U) (x : Bit S) : map g (map f x) = map (g ∘ f) x := by
  cases x <;> rfl

section Lin
variable {m : Type → Type u} [Monad m] [LinM m S]

/-- A share of a constant. -/
def share (b : Bool) : m (Bit S) := do
  let s ← bconst b
  pure (var s)

/-- Xor with folding: a constant `false` is dropped, two constants fold,
`x ⊕ 1` is one (free) xor with a shared `1`. -/
def xor (x y : Bit S) : m (Bit S) :=
  match x, y with
  | const a, const b => pure (const (a ^^ b))
  | const false, var s => pure (var s)
  | const true, var s => do
    let o ← bconst true
    let r ← bxor s o
    pure (var r)
  | var s, const false => pure (var s)
  | var s, const true => do
    let o ← bconst true
    let r ← bxor s o
    pure (var r)
  | var s, var t => do
    let r ← bxor s t
    pure (var r)

/-- Turn a wire into a share (a constant is shared, for free). -/
def materialize (x : Bit S) : m S :=
  match x with
  | const b => bconst b
  | var s => pure s

end Lin

section And
variable {m : Type → Type u} [Monad m] [BitM m S]

/-- And with folding: a constant `false` kills, a constant `true` is dropped. -/
def and (x y : Bit S) : m (Bit S) :=
  match x, y with
  | const a, const b => pure (const (a && b))
  | const false, var _ => pure (const false)
  | const true, var s => pure (var s)
  | var _, const false => pure (const false)
  | var s, const true => pure (var s)
  | var s, var t => do
    let r ← band s t
    pure (var r)

/-- `z ⊕ (x ∧ (y ⊕ z))`: one AND unless folding removes it. -/
def ch3 (x y z : Bit S) : m (Bit S) := do
  let t ← xor y z
  let p ← and x t
  xor z p

/-- Majority as `x ⊕ ((x ⊕ y) ∧ (x ⊕ z))`, one AND; with two constant
operands the answer is known without one. -/
def maj3 (x y z : Bit S) : m (Bit S) :=
  match x, y, z with
  | const a, const b, const c => pure (const ((a && b) ^^ ((a && c) ^^ (b && c))))
  | const a, const b, var s => if a = b then pure (const a) else pure (var s)
  | const a, var s, const c => if a = c then pure (const a) else pure (var s)
  | var s, const b, const c => if b = c then pure (const b) else pure (var s)
  | x, y, z => do
    let t ← xor x y
    let u ← xor x z
    let p ← and t u
    xor x p

end And

end Bit

/-- `Fin.cons` by a match on the index.  (Mathlib's `Fin.cons` goes through
`Fin.induction`, whose compiled form evaluates every intermediate step,
which is exponential in the nesting depth.) -/
def consFin {n : Nat} {α : Type} (a : α) (rest : Fin n → α) (i : Fin (n + 1)) : α :=
  match h : i.val with
  | 0 => a
  | j + 1 => rest ⟨j, by have := i.isLt; omega⟩

@[simp] theorem consFin_zero {n : Nat} {α : Type} (a : α) (rest : Fin n → α) : consFin a rest 0 = a := rfl
@[simp] theorem consFin_succ {n : Nat} {α : Type} (a : α) (rest : Fin n → α) (i : Fin n) :
    consFin a rest i.succ = rest i := by
  simp [consFin]

/-- A vector of monadic results, built first-to-last. -/
def vecM {m : Type → Type u} [Monad m] {α : Type} : (n : Nat) → (Fin n → m α) → m (Fin n → α)
  | 0, _ => pure fun i => i.elim0
  | n + 1, g => do
    let a ← g 0
    let rest ← vecM n fun i => g i.succ
    pure (consFin a rest)

/-- The list of the values of a function on `Fin n`, first-to-last.  (Core's
`List.ofFn` goes through arrays, which the certificate checker rejects.) -/
def finList {α : Type} : (n : Nat) → (Fin n → α) → List α
  | 0, _ => []
  | n + 1, f => f 0 :: finList n fun i => f i.succ

theorem finList_eq_ofFn {α : Type} : ∀ (n : Nat) (f : Fin n → α), finList n f = List.ofFn f
  | 0, _ => rfl
  | n + 1, f => by
    rw [List.ofFn_succ]
    simp only [finList, finList_eq_ofFn n]

theorem finList_map {α β : Type} (g : α → β) : ∀ (n : Nat) (f : Fin n → α), (finList n f).map g = finList n (g ∘ f)
  | 0, _ => rfl
  | n + 1, f => by
    simp only [finList, List.map_cons, finList_map g n]
    rfl

/-- A list of monadic results, first-to-last. -/
def listM {m : Type → Type u} [Monad m] {α β : Type} (f : α → m β) : List α → m (List β)
  | [] => pure []
  | a :: as => do
    let b ← f a
    let bs ← listM f as
    pure (b :: bs)

/-- Monadic left fold, first-to-last. -/
def foldM {m : Type → Type u} [Monad m] {α β : Type} (f : β → α → m β) : β → List α → m β
  | b, [] => pure b
  | b, a :: as => do
    let b' ← f b a
    foldM f b' as

/-- A 32-bit word of wires, least significant bit first. -/
abbrev Word (S : Type) := Fin 32 → Bit S

namespace Word
variable {S T : Type}

def map (f : S → T) (w : Word S) : Word T := fun i => (w i).map f

/-- A word of shares. -/
def ofShares (w : Fin 32 → S) : Word S := fun i => .var (w i)

/-- The bits of a public constant, least significant first. -/
def const (n : Nat) : Word S := fun i => .const (n.testBit i)

variable {m : Type → Type u} [Monad m] [LinM m S]

/-- Bitwise xor. -/
def xor (x y : Word S) : m (Word S) := vecM 32 fun i => Bit.xor (x i) (y i)

/-- Xor of three words. -/
def xor3 (x y z : Word S) : m (Word S) := do
  let t ← xor x y
  xor t z

/-- Rotate right by `n` (bit `i` of the result is bit `i + n` of the input). -/
def rotr (w : Word S) (n : Nat) : Word S := fun i => w ⟨(i.val + n) % 32, Nat.mod_lt _ (by decide)⟩

/-- Shift right by `n`: the top `n` bits are constant `false`. -/
def shr (w : Word S) (n : Nat) : Word S := fun i =>
  if h : i.val + n < 32 then w ⟨i.val + n, h⟩ else .const false

/-- Every wire as a share. -/
def materialize (w : Word S) : m (Fin 32 → S) := vecM 32 fun i => (w i).materialize

end Word

end WeftChals
