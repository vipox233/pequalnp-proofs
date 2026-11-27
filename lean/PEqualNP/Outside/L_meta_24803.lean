import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24803

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [0, 1]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.and, [6, 10]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.or, [11, 13]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_24803

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_24803 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2117565 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24803.circuit, PEqualNP.Outside.L_meta_24803.shape, by decide, by decide +kernel⟩
