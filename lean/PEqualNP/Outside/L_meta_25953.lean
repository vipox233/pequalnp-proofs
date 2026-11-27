import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25953

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 16 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 9]⟩, ⟨GateOp.and, [8, 10]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [12, 13]⟩], 14⟩

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

theorem small : circ.size ≤ 7 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 13, 13, 3] : List ℕ).getD u.val 0).testBit v.val) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_25953

theorem PEqualNP.Outside.L_meta_25953 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 13, 13, 3] : List ℕ).getD u.val 0).testBit v.val) C := by
  exact ⟨PEqualNP.Outside.L_meta_25953.circ, PEqualNP.Outside.L_meta_25953.fits, PEqualNP.Outside.L_meta_25953.small, PEqualNP.Outside.L_meta_25953.right⟩
