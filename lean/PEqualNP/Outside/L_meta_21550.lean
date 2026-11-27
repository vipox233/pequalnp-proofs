import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21550

open PEqualNP.CircuitLowerBounds

def circuit : Circuit where
  gates := [
    ⟨GateOp.not, [1]⟩,
    ⟨GateOp.and, [3, 5]⟩,
    ⟨GateOp.not, [0]⟩,
    ⟨GateOp.and, [4, 7]⟩,
    ⟨GateOp.or, [6, 8]⟩,
    ⟨GateOp.not, [9]⟩]
  output := 10

theorem shape : PEqualNP.MetaComplexity.FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

end PEqualNP.Outside.L_meta_21550

set_option maxRecDepth 100000 in
theorem PEqualNP.Outside.L_meta_21550 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4567 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_21550.circuit, PEqualNP.Outside.L_meta_21550.shape, by decide, by decide +kernel⟩
