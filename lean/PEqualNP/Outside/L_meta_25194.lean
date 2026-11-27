import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25194

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [4, 3]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [0, 7]⟩,
    ⟨GateOp.and, [6, 1]⟩,
    ⟨GateOp.and, [2, 8]⟩,
    ⟨GateOp.or, [2, 9]⟩,
    ⟨GateOp.or, [11, 0]⟩,
    ⟨GateOp.not, [10, 10]⟩,
    ⟨GateOp.and, [12, 13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25194

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25194 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18235 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25194.circuit, PEqualNP.Outside.L_meta_25194.shape, by decide, by decide +kernel⟩
