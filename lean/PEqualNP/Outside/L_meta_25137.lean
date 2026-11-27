import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25137

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [4, 0]⟩,
    ⟨GateOp.or, [7, 5]⟩,
    ⟨GateOp.and, [5, 7]⟩,
    ⟨GateOp.and, [3, 8]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.and, [8, 6]⟩,
    ⟨GateOp.or, [11, 12]⟩,
    ⟨GateOp.not, [13, 13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25137

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25137 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321041 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25137.circuit, PEqualNP.Outside.L_meta_25137.shape, by decide, by decide +kernel⟩
