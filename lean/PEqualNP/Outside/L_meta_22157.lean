import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22157

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 24 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [7, 11]⟩, ⟨GateOp.or, [8, 14]⟩, ⟨GateOp.or, [2, 16]⟩, ⟨GateOp.or, [3, 12]⟩, ⟨GateOp.and, [15, 17]⟩, ⟨GateOp.and, [13, 18]⟩, ⟨GateOp.or, [19, 20]⟩], 21⟩

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

theorem small : circ.size ≤ 12 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (840690 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22157

theorem PEqualNP.Outside.L_meta_22157 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840690 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_22157.circ, PEqualNP.Outside.L_meta_22157.fits, PEqualNP.Outside.L_meta_22157.small, PEqualNP.Outside.L_meta_22157.right⟩
