import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22895

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 24 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.or, [5, 11]⟩, ⟨GateOp.and, [10, 12]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.and, [2, 14]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [16, 17]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.or, [2, 19]⟩, ⟨GateOp.and, [20, 4]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [22, 18]⟩, ⟨GateOp.or, [23, 21]⟩], 24⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (1940206 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22895

theorem PEqualNP.Outside.L_meta_22895 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940206 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  exact ⟨PEqualNP.Outside.L_meta_22895.circ, PEqualNP.Outside.L_meta_22895.fits, PEqualNP.Outside.L_meta_22895.small, PEqualNP.Outside.L_meta_22895.right⟩
