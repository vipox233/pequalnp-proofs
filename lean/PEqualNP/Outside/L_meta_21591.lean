import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21591

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [0, 1]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.not, [6]⟩,
    ⟨GateOp.and, [4, 7]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [5, 8]⟩,
    ⟨GateOp.or, [10, 9]⟩,
    ⟨GateOp.not, [11]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21591

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21591 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (267229 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21591.circuit, PEqualNP.Outside.L_meta_21591.shape, by decide, by decide +kernel⟩
