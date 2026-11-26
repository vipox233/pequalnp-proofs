import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22037

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 24 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [7, 8]⟩, ⟨GateOp.or, [2, 10]⟩, ⟨GateOp.or, [1, 6]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [3, 11]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.and, [13, 16]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.or, [4, 19]⟩, ⟨GateOp.and, [15, 20]⟩], 21⟩

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

theorem right : PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 6) => (816697 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22037

theorem PEqualNP.Outside.L_meta_22037 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816697 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  exact ⟨PEqualNP.Outside.L_meta_22037.circ, PEqualNP.Outside.L_meta_22037.fits, PEqualNP.Outside.L_meta_22037.small, PEqualNP.Outside.L_meta_22037.right⟩
