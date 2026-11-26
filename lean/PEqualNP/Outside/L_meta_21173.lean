import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21173

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 20 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [3, 14]⟩, ⟨GateOp.or, [6, 15]⟩, ⟨GateOp.or, [5, 10]⟩, ⟨GateOp.and, [16, 17]⟩], 18⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 5) => (102301 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_21173

theorem PEqualNP.Outside.L_meta_21173 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (102301 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_21173.circ, PEqualNP.Outside.L_meta_21173.fits, PEqualNP.Outside.L_meta_21173.small, PEqualNP.Outside.L_meta_21173.right⟩
