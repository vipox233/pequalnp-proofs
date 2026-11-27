import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24514

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.or, [0, 9]⟩,
    ⟨GateOp.or, [6, 11]⟩,
    ⟨GateOp.and, [10, 12]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24514

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24514 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24514.circuit, PEqualNP.Outside.L_meta_24514.shape, by decide, by decide +kernel⟩
