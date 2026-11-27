import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22280

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
    ⟨GateOp.or, [13, 5]⟩,
    ⟨GateOp.and, [0, 14]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [11, 15]⟩,
    ⟨GateOp.or, [17, 16]⟩]
  output := 18

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22280

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22280 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16954 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22280.circuit, PEqualNP.Outside.L_meta_22280.shape, by decide, by decide +kernel⟩
