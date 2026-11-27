import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24207

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [3, 6]⟩,
    ⟨GateOp.and, [4, 7]⟩,
    ⟨GateOp.or, [5, 8]⟩,
    ⟨GateOp.not, [9, 9]⟩,
    ⟨GateOp.or, [0, 10]⟩]
  output := 11

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24207

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24207 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582719 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24207.circuit, PEqualNP.Outside.L_meta_24207.shape, by decide, by decide +kernel⟩
