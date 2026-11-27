import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24171

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 15 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.or, [1, 4]⟩, ⟨GateOp.and, [0, 5]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.not, [8]⟩, ⟨GateOp.and, [7, 9]⟩, ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.not, [11]⟩, ⟨GateOp.and, [3, 12]⟩, ⟨GateOp.or, [6, 10]⟩, ⟨GateOp.or, [14, 13]⟩], 15⟩

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

theorem small : circ.size ≤ 11 := by decide

theorem right : ∀ i j : Fin 5, circ.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283354 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24171

theorem PEqualNP.Outside.L_meta_24171 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283354 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_24171.circ, PEqualNP.Outside.L_meta_24171.fits, PEqualNP.Outside.L_meta_24171.small, PEqualNP.Outside.L_meta_24171.right⟩
