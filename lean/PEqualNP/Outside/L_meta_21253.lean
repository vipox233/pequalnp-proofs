import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21253

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 20 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [2, 6]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [3, 13]⟩, ⟨GateOp.or, [7, 9]⟩, ⟨GateOp.and, [9, 14]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.and, [10, 17]⟩, ⟨GateOp.or, [16, 18]⟩], 19⟩

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

theorem small : circ.size ≤ 11 := by decide

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 5) => (36061 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_21253

theorem PEqualNP.Outside.L_meta_21253 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36061 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨PEqualNP.Outside.L_meta_21253.circ, PEqualNP.Outside.L_meta_21253.fits, PEqualNP.Outside.L_meta_21253.small, PEqualNP.Outside.L_meta_21253.right⟩
