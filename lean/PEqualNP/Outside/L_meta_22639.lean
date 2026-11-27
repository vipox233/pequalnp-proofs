import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22639

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 24 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [10, 9]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [5, 13]⟩, ⟨GateOp.and, [1, 14]⟩, ⟨GateOp.or, [4, 6]⟩, ⟨GateOp.and, [2, 16]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [4, 5]⟩, ⟨GateOp.and, [18, 19]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.or, [21, 17]⟩, ⟨GateOp.or, [22, 20]⟩], 23⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (808891 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22639

theorem PEqualNP.Outside.L_meta_22639 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808891 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_22639.circ, PEqualNP.Outside.L_meta_22639.fits, PEqualNP.Outside.L_meta_22639.small, PEqualNP.Outside.L_meta_22639.right⟩
