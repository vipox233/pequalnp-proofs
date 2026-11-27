import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21642

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [1]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.or, [0, 2]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [6, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21642

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21642 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8797 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21642.circuit, PEqualNP.Outside.L_meta_21642.shape, by decide, by decide +kernel⟩
