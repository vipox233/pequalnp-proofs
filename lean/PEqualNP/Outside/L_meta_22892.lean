import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22892

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 24 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [11, 9]⟩, ⟨GateOp.and, [0, 12]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [14, 8]⟩, ⟨GateOp.or, [7, 15]⟩, ⟨GateOp.and, [1, 16]⟩, ⟨GateOp.or, [10, 8]⟩, ⟨GateOp.and, [2, 18]⟩, ⟨GateOp.or, [4, 14]⟩, ⟨GateOp.and, [3, 20]⟩, ⟨GateOp.or, [13, 17]⟩, ⟨GateOp.or, [22, 19]⟩, ⟨GateOp.or, [23, 21]⟩], 24⟩

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

theorem small : circ.size ≤ 15 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (1939371 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22892

theorem PEqualNP.Outside.L_meta_22892 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939371 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  exact ⟨PEqualNP.Outside.L_meta_22892.circ, PEqualNP.Outside.L_meta_22892.fits, PEqualNP.Outside.L_meta_22892.small, PEqualNP.Outside.L_meta_22892.right⟩
