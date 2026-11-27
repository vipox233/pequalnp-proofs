import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22099

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.or, [7, 5]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.and, [2, 9]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.or, [11, 5]⟩,
    ⟨GateOp.and, [0, 12]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [10, 13]⟩,
    ⟨GateOp.or, [15, 14]⟩]
  output := 16

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_22099

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_22099 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17208 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22099.circuit, PEqualNP.Outside.L_meta_22099.shape, by decide, by decide +kernel⟩
