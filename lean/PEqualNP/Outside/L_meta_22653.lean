import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22653

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 24 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [10, 6]⟩, ⟨GateOp.or, [11, 8]⟩, ⟨GateOp.or, [12, 9]⟩, ⟨GateOp.and, [0, 13]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [5, 15]⟩, ⟨GateOp.and, [1, 16]⟩, ⟨GateOp.or, [4, 15]⟩, ⟨GateOp.and, [2, 18]⟩, ⟨GateOp.and, [3, 10]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [21, 19]⟩, ⟨GateOp.or, [22, 20]⟩], 23⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def shapeB (C : Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : Circuit} (h : shapeB C = true) : Monotone2 C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem fits : Monotone2 circ := shapeB_sound (by decide)

theorem small : circ.size ≤ 14 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (840631 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22653

theorem PEqualNP.Outside.L_meta_22653 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840631 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_22653.circ, PEqualNP.Outside.L_meta_22653.fits, PEqualNP.Outside.L_meta_22653.small, PEqualNP.Outside.L_meta_22653.right⟩
