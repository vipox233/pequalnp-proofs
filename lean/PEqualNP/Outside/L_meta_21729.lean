import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21729

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.not, [5]⟩,
    ⟨GateOp.and, [1, 6]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [10, 3]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.and, [2, 13]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [15, 14]⟩]
  output := 16

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21729

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21729 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4442 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21729.circuit, PEqualNP.Outside.L_meta_21729.shape, by decide, by decide +kernel⟩
