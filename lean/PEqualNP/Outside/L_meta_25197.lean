import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25197

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [1, 1]⟩,
    ⟨GateOp.and, [2, 6]⟩,
    ⟨GateOp.or, [5, 4]⟩,
    ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.not, [9, 9]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [9, 7]⟩,
    ⟨GateOp.or, [11, 10]⟩,
    ⟨GateOp.and, [13, 12]⟩]
  output := 14

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_25197

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_25197 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20028 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_25197.circuit, PEqualNP.Outside.L_meta_25197.shape, by decide, by decide +kernel⟩
