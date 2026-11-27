import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21705

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.not, [10]⟩,
    ⟨GateOp.and, [4, 11]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.or, [13, 12]⟩,
    ⟨GateOp.not, [14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21705

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21705 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274963 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21705.circuit, PEqualNP.Outside.L_meta_21705.shape, by decide, by decide +kernel⟩
