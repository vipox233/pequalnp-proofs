import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25389

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.or, [5, 2]⟩,
    ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.and, [1, 6]⟩,
    ⟨GateOp.not, [9, 9]⟩,
    ⟨GateOp.or, [3, 2]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.or, [0, 13]⟩,
    ⟨GateOp.or, [10, 14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25389

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25389 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6377279 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25389.circuit, PEqualNP.Outside.L_meta_25389.shape, by decide, by decide +kernel⟩
