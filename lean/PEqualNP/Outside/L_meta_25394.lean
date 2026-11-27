import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25394

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.and, [3, 7]⟩,
    ⟨GateOp.or, [3, 2]⟩,
    ⟨GateOp.not, [5, 5]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.not, [11, 11]⟩,
    ⟨GateOp.and, [9, 10]⟩,
    ⟨GateOp.or, [13, 7]⟩,
    ⟨GateOp.and, [12, 14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25394

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25394 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408631 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25394.circuit, PEqualNP.Outside.L_meta_25394.shape, by decide, by decide +kernel⟩
