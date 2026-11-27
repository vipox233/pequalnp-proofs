import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21520

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [3]⟩,
    ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [8, 7]⟩]
  output := 9

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21520

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21520 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8927 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21520.circuit, PEqualNP.Outside.L_meta_21520.shape, by decide, by decide +kernel⟩
