import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24175

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 15 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [3, 4]⟩, ⟨GateOp.and, [1, 5]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [2, 7]⟩, ⟨GateOp.not, [0]⟩, ⟨GateOp.and, [4, 9]⟩, ⟨GateOp.or, [2, 7]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.or, [6, 8]⟩, ⟨GateOp.or, [13, 10]⟩, ⟨GateOp.or, [14, 12]⟩, ⟨GateOp.not, [15]⟩], 16⟩

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

theorem small : circ.size ≤ 12 := by decide

theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266334 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24175

theorem PEqualNP.Outside.L_meta_24175 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266334 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_24175.circ, PEqualNP.Outside.L_meta_24175.fits, PEqualNP.Outside.L_meta_24175.small, PEqualNP.Outside.L_meta_24175.right⟩
