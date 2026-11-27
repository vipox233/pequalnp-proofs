import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23454

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.not, [3, 3]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [6, 7]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.not, [10, 10]⟩,
    ⟨GateOp.or, [9, 11]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23454

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23454 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149815 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23454.circuit, PEqualNP.Outside.L_meta_23454.shape, by decide, by decide +kernel⟩
