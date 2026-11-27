import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24362

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.not, [6]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.and, [8, 10]⟩,
    ⟨GateOp.not, [11]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24362

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24362 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274844071 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24362.circuit, PEqualNP.Outside.L_meta_24362.shape, by decide, by decide +kernel⟩
