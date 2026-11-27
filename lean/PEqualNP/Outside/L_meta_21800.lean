import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21800

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [3]⟩,
    ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.and, [2, 8]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [10, 4]⟩,
    ⟨GateOp.not, [11]⟩,
    ⟨GateOp.and, [3, 12]⟩,
    ⟨GateOp.and, [0, 4]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.or, [15, 13]⟩,
    ⟨GateOp.or, [16, 14]⟩]
  output := 17

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21800

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21800 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266974 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21800.circuit, PEqualNP.Outside.L_meta_21800.shape, by decide, by decide +kernel⟩
