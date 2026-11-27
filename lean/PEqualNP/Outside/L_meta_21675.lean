import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21675

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [4]⟩,
    ⟨GateOp.and, [2, 5]⟩,
    ⟨GateOp.and, [1, 4]⟩,
    ⟨GateOp.or, [1, 4]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.and, [3, 9]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.or, [11, 7]⟩,
    ⟨GateOp.or, [12, 10]⟩]
  output := 13

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21675

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21675 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275103 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21675.circuit, PEqualNP.Outside.L_meta_21675.shape, by decide, by decide +kernel⟩
