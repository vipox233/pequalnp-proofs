import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21629

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.not, [5]⟩,
    ⟨GateOp.and, [2, 6]⟩,
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [8, 4]⟩,
    ⟨GateOp.and, [0, 9]⟩,
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [12, 11]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21629

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21629 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4510 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21629.circuit, PEqualNP.Outside.L_meta_21629.shape, by decide, by decide +kernel⟩
