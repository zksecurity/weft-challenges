import WeftChals.Timing.Checkpoint
import Lean

/-!
# Compose kernel-checked timing evaluations

The evaluator proposes finite snapshots using compiled code. `checked` asks the
kernel to verify each proposal against the original computation. Only those
checked equality proofs enter the final theorem; no native-decision axiom is used.
-/
namespace WeftChals.Timing
open Lean Meta Elab Command

private def checked (type proof : Expr) : MetaM Expr := do
  let name ← withOptions (Elab.async.set · false) do
    mkAuxLemma [] type proof
  return mkConst name

private structure Result where
  value : Expr
  count : Expr
  proof : Expr

private def liftExpr (action : MetaM Expr) : CommandElabM Expr :=
  liftTermElabM do instantiateMVars (← action)

private unsafe def checkpoint (x : Expr) : MetaM Result := do
  let type ← whnf (← inferType x)
  let α := type.getAppArgs[0]!
  let encoded ← mkAppM ``encode #[x]
  let candidate ← profileitM Exception "timing proposal" (← getOptions) do
    evalExpr (Nat × List (List Nat)) (← inferType encoded) encoded
  let rhs ← mkAppOptM ``decode #[some α, none, some (toExpr candidate)]
  let rhsEncoded ← mkAppM ``encode #[rhs]
  let eqType ← mkEq encoded rhsEncoded
  let h ← profileitM Exception "timing checkpoint" (← getOptions) do
    checked eqType (← mkDecideProof eqType)
  let proof ← mkAppM ``encode_injective #[h]
  let proof ← checked (← mkEq x rhs) proof
  return ⟨← instantiateMVars (← mkAppM ``_root_.Prod.fst #[rhs]), toExpr candidate.1, proof⟩

/-- Each kernel call checks just one transition with concrete inputs. -/
private unsafe def evalFold (f seed xs : Expr) : CommandElabM Result := do
  let rec go (s xs : Expr) : CommandElabM Result := do
    let xs' ← liftExpr (whnf xs)
    if xs'.isAppOf ``List.nil then
      return ⟨s, toExpr (0 : Nat), ← liftExpr (mkAppM ``fold_nil #[f, s])⟩
    unless xs'.isAppOf ``List.cons do
      throwError "timing evaluation expected a concrete list"
    let args := xs'.getAppArgs
    let a := args[1]!
    let as := args[2]!
    let head ← liftTermElabM (checkpoint (mkApp2 f s a))
    let tail ← go head.value as
    liftTermElabM do
      let proof ← mkAppM ``fold_cons #[f, s, head.value, tail.value, a, as,
        head.count, tail.count, head.proof, tail.proof]
      let count ← whnf (← mkAppM ``Nat.add #[head.count, tail.count])
      let proof ← checked (← inferType proof) proof
      return ⟨tail.value, count, proof⟩
  go seed xs

syntax (name := checkpointTimeModel) "time_model_result " ident " := " term:arg term:arg term:arg : command

@[command_elab checkpointTimeModel]
private unsafe def evalTimeModel : CommandElab := fun stx => do
  let `(command| time_model_result $name := $p $h $b) := stx | throwUnsupportedSyntax
  let model ← liftTermElabM do
    let model ← Term.elabTerm (← `(timeModel $p $h $b)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars model
  let args := model.getAppArgs
  let p := args[0]!
  let h := args[1]!
  let b := args[2]!
  let zero ← liftTermElabM do
    let zeroExpr ← Term.elabTerm (← `(Compress.constW (m := Count) (S := Nat) 0)) none
    checkpoint (← instantiateMVars zeroExpr)
  let scheduleFn ← liftExpr <| mkAppOptM ``Compress.scheduleStep
    #[some (mkConst ``Count), none, some (mkConst ``Nat), none, some zero.value]
  let block ← liftExpr <| mkAppM ``finList #[toExpr (16 : Nat), b]
  let schedulePlans ← liftExpr <| mkAppM ``Compress.schedulePlans #[p]
  let schedule ← evalFold scheduleFn block schedulePlans
  let roundFn ← liftExpr <| mkAppOptM ``Compress.round
    #[some (mkConst ``Count), none, some (mkConst ``Nat), none]
  let initial ← liftExpr <| mkAppM ``initial #[h]
  let roundPlans ← liftExpr <| mkAppM ``Compress.roundPlans #[p]
  let roundArgs ← liftExpr <| mkAppM ``List.zip #[schedule.value, roundPlans]
  let roundArgs ← liftExpr <| mkAppM ``List.zip #[mkConst ``Compress.kList, roundArgs]
  let rounds ← evalFold roundFn initial roundArgs
  let final ← liftTermElabM do checkpoint (← mkAppM ``finish #[p, h, rounds.value])
  let declName := (← getCurrNamespace) ++ name.getId
  liftTermElabM do
    let proof ← mkAppM ``compose #[p, h, b, zero.value, schedule.value, rounds.value,
      final.value, zero.count, schedule.count, rounds.count, final.count,
      zero.proof, schedule.proof, rounds.proof, final.proof]
    addDecl <| .thmDecl {name := declName, levelParams := [], type := ← inferType proof, value := proof}

end WeftChals.Timing
