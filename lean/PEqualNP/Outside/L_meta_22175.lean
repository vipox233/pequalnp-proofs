import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22175

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [6, 3]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [8, 5]⟩,
    ⟨GateOp.not, [9]⟩,
    ⟨GateOp.and, [2, 10]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [12, 4]⟩,
    ⟨GateOp.and, [0, 13]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [11, 14]⟩,
    ⟨GateOp.or, [16, 15]⟩]
  output := 17

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22175

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22175 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16922 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22175.circuit, PEqualNP.Outside.L_meta_22175.shape, by decide, by decide +kernel⟩
