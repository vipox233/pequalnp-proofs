import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21490

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [7, 6]⟩]
  output := 8

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21490

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21490 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8735 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21490.circuit, PEqualNP.Outside.L_meta_21490.shape, by decide, by decide +kernel⟩
