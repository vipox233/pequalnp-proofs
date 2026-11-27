import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22900

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 24 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [6, 7]⟩, ⟨GateOp.or, [11, 9]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [14, 8]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.or, [17, 7]⟩, ⟨GateOp.and, [16, 18]⟩, ⟨GateOp.or, [17, 6]⟩, ⟨GateOp.and, [3, 20]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [22, 19]⟩, ⟨GateOp.or, [23, 21]⟩], 24⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (1948668 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22900

theorem PEqualNP.Outside.L_meta_22900 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948668 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  exact ⟨PEqualNP.Outside.L_meta_22900.circ, PEqualNP.Outside.L_meta_22900.fits, PEqualNP.Outside.L_meta_22900.small, PEqualNP.Outside.L_meta_22900.right⟩
