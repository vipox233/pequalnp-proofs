import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21477

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 3]⟩,
    ⟨GateOp.or, [6, 4]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [9, 4]⟩,
    ⟨GateOp.and, [1, 10]⟩,
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [2, 12]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [15, 13]⟩,
    ⟨GateOp.or, [16, 14]⟩]
  output := 17

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21477

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21477 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (549790 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21477.circuit, PEqualNP.Outside.L_meta_21477.shape, by decide, by decide +kernel⟩
