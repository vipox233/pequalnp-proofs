import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23142

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 18 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [9, 8]⟩, ⟨GateOp.or, [3, 10]⟩, ⟨GateOp.and, [0, 11]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.and, [1, 13]⟩, ⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [2, 15]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [17, 16]⟩], 18⟩

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

theorem small : circ.size ≤ 10 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 3) (v : Fin 6) => (14125 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_23142

theorem PEqualNP.Outside.L_meta_23142 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14125 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_23142.circ, PEqualNP.Outside.L_meta_23142.fits, PEqualNP.Outside.L_meta_23142.small, PEqualNP.Outside.L_meta_23142.right⟩
