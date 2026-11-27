import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21689

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.not, [5]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [0, 3]⟩,
    ⟨GateOp.not, [8]⟩,
    ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.not, [11]⟩,
    ⟨GateOp.and, [2, 12]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [14, 13]⟩]
  output := 15

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21689

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21689 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13017 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21689.circuit, PEqualNP.Outside.L_meta_21689.shape, by decide, by decide +kernel⟩
