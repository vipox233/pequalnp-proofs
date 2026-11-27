import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21467

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.or, [5, 4]⟩,
    ⟨GateOp.and, [0, 6]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [1, 8]⟩,
    ⟨GateOp.and, [2, 3]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [11, 10]⟩]
  output := 12

theorem shape : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21467

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21467 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8598 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21467.circuit, PEqualNP.Outside.L_meta_21467.shape, by decide, by decide +kernel⟩
