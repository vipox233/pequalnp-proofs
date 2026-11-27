import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21581

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [1]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.and, [1, 7]⟩,
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [11, 10]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21581

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21581 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13277 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21581.circuit, PEqualNP.Outside.L_meta_21581.shape, by decide, by decide +kernel⟩
