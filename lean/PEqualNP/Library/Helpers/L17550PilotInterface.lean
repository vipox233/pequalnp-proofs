import PEqualNP.Library.Helpers.L17550Bounded

open PEqualNP.MetaComplexity.L17550Projection.Bounded

namespace MaskPilotInterface

private theorem read_fold (w : List Word) :
    w.foldr (fun wire (rest : Idx → Word) index =>
      if index = 0 then wire else rest (index - 1)) (fun _ => 0) = read w := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    rw [List.foldr_cons, ih]
    funext i
    rfl

private theorem budget_fold (gs : List Op) :
    gs.foldr (fun gate (rest : Bool → Bool) used =>
      (!(used && gate.1)) && rest (used || gate.1)) (fun _ => true) =
      (fun u => withinAndBudget u gs) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldr_cons, ih]
    rfl

def Statement (k q : Nat) : Prop :=
∀ (gates : Fin k → Bool × BitVec 5 × BitVec 5)
    (pairs : Fin q → BitVec 5 × BitVec 5),
  let read := fun (bank : List (BitVec 21)) =>
    bank.foldr (fun wire (rest : BitVec 5 → BitVec 21) index =>
      if index = 0 then wire else rest (index - 1)) (fun _ => 0)
  let product := fun (bank : List (BitVec 21)) (pair : BitVec 5 × BitVec 5) =>
    read bank pair.1 &&& read bank pair.2
  let program := List.ofFn gates
  let bank := program.foldl (fun bank gate => bank ++
    [if gate.1 then product bank gate.2 else read bank gate.2.1 ||| read bank gate.2.2])
    (([63491,1386508,235568,0,151748,287504,0,0,558408,1246721,1835170,0,1246721,1835170,0,0] : List Nat).map (BitVec.ofNat 21))
  let affordable := program.foldr (fun gate (rest : Bool → Bool) used =>
    (!(used && gate.1)) && rest (used || gate.1)) (fun _ => true) false
  let terminals := List.ofFn pairs
  (affordable && terminals.all (fun pair => (product bank pair &&& 2095104) == 0) &&
    ((terminals.foldl (fun acc pair => acc ||| product bank pair) 0 &&& 2047) == 2047)) = false

theorem to_bounded (k q : Nat) : Statement k q ↔ Reject k q := by
  unfold Statement Reject
  dsimp only
  simp_rw [read_fold, budget_fold]
  rfl

end MaskPilotInterface
