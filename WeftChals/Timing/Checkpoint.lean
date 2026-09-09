import WeftChals.Realization.Cost

/-!
# Checked timing checkpoints

A checkpoint records concrete arrival times and an AND count. Native evaluation
only proposes these numbers; each checkpoint is proved by kernel reduction before
it can be used to compose the next step.
-/
namespace WeftChals.Timing

def word (xs : List Nat) : Wd Nat := fun i => xs.getD i.val 0

theorem getD_finList {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) (d : α) :
    (finList n f).getD i.val d = f i := by
  rw [finList_eq_ofFn, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

theorem word_finList (w : Wd Nat) : word (finList 32 w) = w := by
  funext i
  exact getD_finList w i 0

/-- A finite representation of the state between checked computations. -/
class Snapshot (α : Type) where
  encode : α → List (List Nat)
  decode : List (List Nat) → α
  decode_encode : ∀ a, decode (encode a) = a

instance : Snapshot (Wd Nat) where
  encode w := [finList 32 w]
  decode ws := word (ws.getD 0 [])
  decode_encode w := by simp [List.getD, word_finList]

instance : Snapshot (List (Wd Nat)) where
  encode ws := ws.map (finList 32)
  decode ws := ws.map word
  decode_encode ws := by simp [List.map_map, Function.comp_def, word_finList]

instance : Snapshot (Compress.State Nat) where
  encode s := [finList 32 s.a, finList 32 s.b, finList 32 s.c, finList 32 s.d,
    finList 32 s.e, finList 32 s.f, finList 32 s.g, finList 32 s.h]
  decode ws := ⟨word (ws.getD 0 []), word (ws.getD 1 []), word (ws.getD 2 []),
    word (ws.getD 3 []), word (ws.getD 4 []), word (ws.getD 5 []),
    word (ws.getD 6 []), word (ws.getD 7 [])⟩
  decode_encode s := by cases s; simp [List.getD, word_finList]

instance {n : Nat} : Snapshot (Fin n → Wd Nat) where
  encode ws := finList n fun i => finList 32 (ws i)
  decode ws := fun i => word (ws.getD i.val [])
  decode_encode ws := by
    funext i
    rw [getD_finList, word_finList]

/-- Store the local AND count alongside finite output arrival times. -/
def encode {α : Type} [Snapshot α] (x : Count α) : Nat × List (List Nat) :=
  (x.2, Snapshot.encode x.1)

def decode {α : Type} [Snapshot α] (x : Nat × List (List Nat)) : Count α :=
  (Snapshot.decode x.2, x.1)

theorem encode_injective {α : Type} [Snapshot α] {x y : Count α}
    (h : encode x = encode y) : x = y := by
  have := congrArg (decode (α := α)) h
  simpa [decode, encode, Snapshot.decode_encode] using this

theorem fold_nil {α β : Type} (f : β → α → Count β) (s : β) :
    foldM f s [] = (s, 0) := rfl

theorem fold_cons {α β : Type} (f : β → α → Count β) (s t u : β)
    (a : α) (as : List α) (c d : Nat)
    (head : f s a = (t, c)) (tail : foldM f t as = (u, d)) :
    foldM f s (a :: as) = (u, c + d) := by
  simp only [foldM, head, Writer.bind_eq, Writer.bind, tail, Acc.nat_app]

def initial (H : Fin 8 → Wd Nat) : Compress.State Nat :=
  ⟨H 0, H 1, H 2, H 3, H 4, H 5, H 6, H 7⟩

def finish (plan : BlockPlan) (H : Fin 8 → Wd Nat) (s : Compress.State Nat) :
    Count (Fin 8 → Wd Nat) :=
  let outs : Fin 8 → Wd Nat := consFin s.a (consFin s.b (consFin s.c (consFin s.d
    (consFin s.e (consFin s.f (consFin s.g (consFin s.h fun i => i.elim0)))))))
  vecM 8 fun i => WordM.add (plan.final.getD i ⟨31, []⟩) (H i) (outs i)

theorem compose (plan : BlockPlan) (H : Fin 8 → Wd Nat) (block : Fin 16 → Wd Nat)
    (z : Wd Nat) (W : List (Wd Nat)) (s : Compress.State Nat) (out : Fin 8 → Wd Nat)
    (cz cw cs co : Nat)
    (hz : Compress.constW (m := Count) 0 = (z, cz))
    (hw : foldM (m := Count) (Compress.scheduleStep z) (finList 16 block) (Compress.schedulePlans plan) = (W, cw))
    (hs : foldM (m := Count) Compress.round (initial H)
      (List.zip Compress.kList (List.zip W (Compress.roundPlans plan))) = (s, cs))
    (ho : finish plan H s = (out, co)) :
    timeModel plan H block = (out, cz + (cw + (cs + co))) := by
  change Writer.bind (Compress.constW (m := Count) 0) (fun z =>
    Writer.bind (foldM (Compress.scheduleStep z) (finList 16 block) (Compress.schedulePlans plan)) (fun W =>
      Writer.bind (foldM Compress.round (initial H)
        (List.zip Compress.kList (List.zip W (Compress.roundPlans plan)))) (finish plan H))) = _
  simp only [hz, Writer.bind, hw, hs, ho, Acc.nat_app]

end WeftChals.Timing
