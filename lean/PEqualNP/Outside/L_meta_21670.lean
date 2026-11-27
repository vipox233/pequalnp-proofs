import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21670

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [1, 5]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.not, [7]⟩,
    ⟨GateOp.and, [4, 8]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩,
    ⟨GateOp.not, [12]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21670

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21670 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266847 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21670.circuit, PEqualNP.Outside.L_meta_21670.shape, by decide, by decide +kernel⟩
