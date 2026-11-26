import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20552

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact SAT search, right on the 25 promise inputs.
def circ : Circuit := ⟨[⟨GateOp.or, [2, 5]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 9]⟩, ⟨GateOp.and, [11, 12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.and, [10, 13]⟩, ⟨GateOp.not, [15]⟩, ⟨GateOp.or, [16, 17]⟩], 18⟩

def okOp : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def shapeB (C : Circuit) : Bool :=
  C.gates.all fun g => okOp g.op && decide (g.inputs.length ≤ 2)

theorem shapeB_sound {C : Circuit} (h : shapeB C = true) : FanInTwo C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [okOp]

theorem fits : FanInTwo circ := shapeB_sound (by decide)

theorem small : circ.size ≤ 9 := by decide

theorem right : PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236582 : ℕ).testBit (5 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_20552

theorem PEqualNP.Outside.L_meta_20552 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16236582 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨PEqualNP.Outside.L_meta_20552.circ, PEqualNP.Outside.L_meta_20552.fits, PEqualNP.Outside.L_meta_20552.small, PEqualNP.Outside.L_meta_20552.right⟩
