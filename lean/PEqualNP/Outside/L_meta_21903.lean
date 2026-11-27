import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21903

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [0, 7]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.and, [1, 9]⟩,
    ⟨GateOp.or, [8, 10]⟩]
  output := 11

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21903

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21903 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (1836 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21903.circuit, PEqualNP.Outside.L_meta_21903.shape, by decide, by decide +kernel⟩
