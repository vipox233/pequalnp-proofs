import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23836

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 15 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 6]⟩, ⟨GateOp.or, [5, 7]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.or, [9, 10]⟩], 11⟩

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

theorem small : circ.size ≤ 7 := by decide

theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4187 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_23836

theorem PEqualNP.Outside.L_meta_23836 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4187 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_23836.circ, PEqualNP.Outside.L_meta_23836.fits, PEqualNP.Outside.L_meta_23836.small, PEqualNP.Outside.L_meta_23836.right⟩
