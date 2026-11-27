import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21694

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.and, [0, 5]⟩,
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.and, [4, 7]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.or, [12, 10]⟩,
    ⟨GateOp.or, [13, 11]⟩,
    ⟨GateOp.not, [14]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21694

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21694 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266320 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21694.circuit, PEqualNP.Outside.L_meta_21694.shape, by decide, by decide +kernel⟩
