import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21524

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [0, 3]⟩,
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.and, [4, 6]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.not, [8]⟩]
  output := 9

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21524

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21524 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274903 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21524.circuit, PEqualNP.Outside.L_meta_21524.shape, by decide, by decide +kernel⟩
