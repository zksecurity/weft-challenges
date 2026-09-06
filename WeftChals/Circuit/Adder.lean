import WeftChals.Circuit.BitM
import WeftChals.Circuit.Plan

/-!
# The carry-prefix adder, driven by a network

`Adder.add net x y` adds two words modulo `2^32` with the carries computed
by the productions of `net` (see `Net`).  Leading bit positions where one
operand is a constant `false` generate no carry and are skipped, exactly
as the Python generator's `add32_dp` does; the network then addresses the
remaining positions as elements `0, 1, …`.

The builder is total and correct whatever the productions say: a range
that was never produced is computed by a ripple of majorities, and a
network whose size does not match the positions is ignored.  Cost is
what the exported networks make it.
-/
namespace WeftChals

universe u
variable {m : Type → Type u} [Monad m] {S : Type} [BitM m S]

namespace Adder

/-- Is a wire the constant `false`? -/
def Bit.isZero : Bit S → Bool
  | .const false => true
  | _ => false

/-- Range values computed so far: `(isG, a, b) ↦ wire`. -/
abbrev Env (S : Type) := List ((Bool × Nat × Nat) × Bit S)

def Env.find (e : Env S) (key : Bool × Nat × Nat) : Option (Bit S) :=
  (e.find? fun p => p.1 = key).map (·.2)

/-- The two operands and the bit positions the network's elements stand for. -/
structure Ctx (S : Type) where
  x : Word S
  y : Word S
  pos : List Nat

/-- Bit `k` (an element index) of an operand. -/
def Ctx.bit (c : Ctx S) (w : Word S) (k : Nat) : Bit S :=
  w ⟨c.pos.getD k 0 % 32, Nat.mod_lt _ (by decide)⟩

/-- The generate of one element, `x ∧ y`, memoised. -/
def leafG (c : Ctx S) (e : Env S) (k : Nat) : m (Bit S × Env S) :=
  match e.find (true, k, k) with
  | some w => pure (w, e)
  | none => do
    let w ← Bit.and (c.bit c.x k) (c.bit c.y k)
    pure (w, ((true, k, k), w) :: e)

/-- The propagate of one element, `x ⊕ y` (free). -/
def leafP (c : Ctx S) (k : Nat) : m (Bit S) := Bit.xor (c.bit c.x k) (c.bit c.y k)

/-- `G[a..b]` by a ripple of majorities from the leaf at `a`. -/
def rippleG (c : Ctx S) (e : Env S) (a b : Nat) : m (Bit S × Env S) := do
  let r ← leafG c e a
  let g ← foldM (fun g k => Bit.maj3 (c.bit c.x k) (c.bit c.y k) g) r.1 (List.range' (a + 1) (b - a))
  pure (g, r.2)

/-- `P[a..b]` by a chain of ands. -/
def rippleP (c : Ctx S) (a b : Nat) : m (Bit S) := do
  let p ← leafP c a
  foldM (fun p k => do let q ← leafP c k; Bit.and p q) p (List.range' (a + 1) (b - a))

/-- `G[a..b]`: a leaf, a produced range, or (fallback) a ripple. -/
def getG (c : Ctx S) (e : Env S) (a b : Nat) : m (Bit S × Env S) :=
  if a = b then leafG c e a
  else match e.find (true, a, b) with
    | some w => pure (w, e)
    | none => rippleG c e a b

/-- `P[a..b]`: a leaf, a produced range, or (fallback) a chain. -/
def getP (c : Ctx S) (e : Env S) (a b : Nat) : m (Bit S) :=
  if a = b then leafP c a
  else match e.find (false, a, b) with
    | some w => pure w
    | none => rippleP c a b

/-- One production. -/
def prod (c : Ctx S) (e : Env S) (code : Nat) : m (Env S) :=
  let p := Prod.decode code
  if p.a ≤ p.m ∧ p.m < p.b ∧ p.b < c.pos.length then
    if p.isG then
      if p.m + 1 = p.b then do
        let lo ← getG c e p.a p.m
        let w ← Bit.maj3 (c.bit c.x p.b) (c.bit c.y p.b) lo.1
        pure (((true, p.a, p.b), w) :: lo.2)
      else do
        let hi ← getG c e (p.m + 1) p.b
        let phi ← getP c hi.2 (p.m + 1) p.b
        let lo ← getG c hi.2 p.a p.m
        let t ← Bit.and phi lo.1
        let w ← Bit.xor hi.1 t
        pure (((true, p.a, p.b), w) :: lo.2)
    else do
      let phi ← getP c e (p.m + 1) p.b
      let plo ← getP c e p.a p.m
      let w ← Bit.and phi plo
      pure (((false, p.a, p.b), w) :: e)
  else pure e

/-- The carries `G[0..k]` for every element `k`, in order. -/
def carries (c : Ctx S) (e : Env S) : m (List (Bit S)) := do
  let r ← foldM (fun (acc : List (Bit S) × Env S) k => do
      let g ← getG c acc.2 0 k
      pure (acc.1 ++ [g.1], g.2)) ([], e) (List.range c.pos.length)
  pure r.1

/-- The carry into bit `i`. -/
def carryInto (p0 : Nat) (cs : List (Bit S)) (i : Fin 32) : Bit S :=
  if i.val = 0 then .const false
  else if i.val - 1 < p0 then .const false
  else cs.getD (i.val - 1 - p0) (.const false)

/-- The context of an addition: the operands and the positions that carry
(leading positions where an operand is a constant `false` are dropped). -/
def mkCtx (x y : Word S) : Ctx S :=
  ⟨x, y, (List.range 31).dropWhile fun i =>
    Bit.isZero (x ⟨i % 32, Nat.mod_lt _ (by decide)⟩) || Bit.isZero (y ⟨i % 32, Nat.mod_lt _ (by decide)⟩)⟩

/-- Addition in a context, with the network `net`. -/
def addWith (net : Net) (c : Ctx S) : m (Word S) := do
  let prods := if net.n = c.pos.length then net.prods else []
  let e ← foldM (prod c) [] prods
  let cs ← carries c e
  let p0 := c.pos.headD 31
  vecM 32 fun i => do
    let p ← Bit.xor (c.x i) (c.y i)
    Bit.xor p (carryInto p0 cs i)

/-- Modular addition of two words with the network `net`. -/
def add (net : Net) (x y : Word S) : m (Word S) := addWith net (mkCtx x y)

end Adder

end WeftChals
