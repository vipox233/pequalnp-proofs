import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49885

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.not, [3]⟩, ⟨.and, [1, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [6, 10]⟩], 11⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

theorem witnessReads : NestedCover.ReadsBack 6 witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_49885

theorem PEqualNP.Outside.L_meta_49885 : ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (10 : Nat).testBit t.val ∧
    w.getD q.val false = (12 : Nat).testBit t.val ∧
    w.getD r.val false = (18 : Nat).testBit t.val :=
  ⟨PEqualNP.Outside.L_meta_49885.witness, ⟨11, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, PEqualNP.Outside.L_meta_49885.witnessFit, PEqualNP.Outside.L_meta_49885.witnessReads,
    by decide, by decide, by decide +kernel⟩
