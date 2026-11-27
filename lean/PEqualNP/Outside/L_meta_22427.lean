import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22427

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [6, 5]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [10, 3]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.or, [12, 5]⟩,
    ⟨GateOp.not, [13]⟩,
    ⟨GateOp.and, [2, 14]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [1, 16]⟩,
    ⟨GateOp.or, [9, 15]⟩,
    ⟨GateOp.or, [18, 17]⟩]
  output := 19

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22427

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22427 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17945 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22427.circuit, PEqualNP.Outside.L_meta_22427.shape, by decide, by decide +kernel⟩
