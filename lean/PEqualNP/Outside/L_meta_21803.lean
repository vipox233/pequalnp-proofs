import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21803

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [3]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.or, [2, 4]⟩,
    ⟨GateOp.and, [1, 7]⟩,
    ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [10, 2]⟩,
    ⟨GateOp.or, [11, 4]⟩,
    ⟨GateOp.not, [12]⟩,
    ⟨GateOp.and, [3, 13]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [15, 9]⟩,
    ⟨GateOp.or, [16, 14]⟩]
  output := 17

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21803

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21803 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279191 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21803.circuit, PEqualNP.Outside.L_meta_21803.shape, by decide, by decide +kernel⟩
