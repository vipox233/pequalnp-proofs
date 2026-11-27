import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24278

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- A circuit found by an exact search; right on all 21 inputs of the statement.
def circ : Circuit := ⟨[⟨GateOp.and, [1, 3]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.or, [4, 7]⟩, ⟨GateOp.or, [3, 8]⟩, ⟨GateOp.not, [9]⟩, ⟨GateOp.or, [0, 6]⟩, ⟨GateOp.or, [11, 10]⟩], 12⟩

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

theorem right : ∀ i j : Fin 6, circ.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17343 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  decide +kernel

end PEqualNP.Outside.L_meta_24278

theorem PEqualNP.Outside.L_meta_24278 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17343 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  exact ⟨PEqualNP.Outside.L_meta_24278.circ, PEqualNP.Outside.L_meta_24278.fits, PEqualNP.Outside.L_meta_24278.small, PEqualNP.Outside.L_meta_24278.right⟩
