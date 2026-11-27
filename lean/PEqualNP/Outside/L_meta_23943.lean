import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23943

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.and, [5, 6]⟩,
    ⟨GateOp.and, [2, 7]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.not, [9, 9]⟩,
    ⟨GateOp.and, [10, 11]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_23943

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_23943 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4507 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_23943.circuit, PEqualNP.Outside.L_meta_23943.shape, by decide, by decide +kernel⟩
