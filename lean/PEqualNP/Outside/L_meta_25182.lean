import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25182

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.or, [7, 5]⟩,
    ⟨GateOp.not, [8, 8]⟩,
    ⟨GateOp.or, [1, 0]⟩,
    ⟨GateOp.and, [6, 10]⟩,
    ⟨GateOp.or, [11, 9]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25182

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25182 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17949 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25182.circuit, PEqualNP.Outside.L_meta_25182.shape, by decide, by decide +kernel⟩
