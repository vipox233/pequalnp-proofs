import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25175

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [3, 6]⟩,
    ⟨GateOp.or, [1, 0]⟩,
    ⟨GateOp.not, [8, 8]⟩,
    ⟨GateOp.or, [9, 2]⟩,
    ⟨GateOp.and, [10, 7]⟩,
    ⟨GateOp.and, [6, 1]⟩,
    ⟨GateOp.or, [12, 11]⟩,
    ⟨GateOp.or, [13, 5]⟩,
    ⟨GateOp.not, [14, 14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25175

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25175 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17305 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25175.circuit, PEqualNP.Outside.L_meta_25175.shape, by decide, by decide +kernel⟩
