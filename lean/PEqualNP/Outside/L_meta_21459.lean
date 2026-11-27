import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21459

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [3, 4]⟩,
    ⟨GateOp.and, [2, 5]⟩,
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [8, 6]⟩,
    ⟨GateOp.or, [9, 7]⟩]
  output := 10

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21459

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21459 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (549855 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21459.circuit, PEqualNP.Outside.L_meta_21459.shape, by decide, by decide +kernel⟩
