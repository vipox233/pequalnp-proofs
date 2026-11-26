import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21218

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 20 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [7, 14]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.or, [4, 17]⟩], 18⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 5) => (237371 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_21218

theorem PEqualNP.Outside.L_meta_21218 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (237371 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_21218.circ, PEqualNP.Outside.L_meta_21218.fits, PEqualNP.Outside.L_meta_21218.small, PEqualNP.Outside.L_meta_21218.right⟩
