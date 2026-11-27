import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_26389

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 25 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [2, 11]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.or, [12, 14]⟩], 15⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 3, 28, 28] : List ℕ).getD u.val 0).testBit v.val) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_26389

theorem PEqualNP.Outside.L_meta_26389 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 5) (v : Fin 5) => (([0, 0, 3, 28, 28] : List ℕ).getD u.val 0).testBit v.val) C := by
  exact ⟨PEqualNP.Outside.L_meta_26389.circ, PEqualNP.Outside.L_meta_26389.fits, PEqualNP.Outside.L_meta_26389.small, PEqualNP.Outside.L_meta_26389.right⟩
