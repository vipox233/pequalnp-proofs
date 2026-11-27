import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21528

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.and, [1, 3]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.and, [4, 6]⟩,
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.not, [8]⟩]
  output := 9

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21528

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21528 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (17052383 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21528.circuit, PEqualNP.Outside.L_meta_21528.shape, by decide, by decide +kernel⟩
