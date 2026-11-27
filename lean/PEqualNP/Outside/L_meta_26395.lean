import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26395

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 25 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [2, 10]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.not, [10]⟩, ⟨GateOp.and, [12, 13]⟩, ⟨GateOp.or, [11, 14]⟩], 15⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def shapeB (C : Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : Circuit} (h : shapeB C = true) : FanInTwo C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem fits : FanInTwo circ := shapeB_sound (by decide)

theorem small : circ.size ≤ 6 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 1, 30, 30] : List ℕ).getD u.val 0).testBit v.val) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_26395

theorem PEqualNP.Outside.L_meta_26395 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 1, 30, 30] : List ℕ).getD u.val 0).testBit v.val) C := by
  exact ⟨PEqualNP.Outside.L_meta_26395.circ, PEqualNP.Outside.L_meta_26395.fits, PEqualNP.Outside.L_meta_26395.small, PEqualNP.Outside.L_meta_26395.right⟩
