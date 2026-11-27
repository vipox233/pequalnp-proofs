import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23901_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.not, [5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [0, 8]⟩,
    ⟨.or, [7, 9]⟩], 10⟩

end PEqualNP.Outside.L_meta_23901_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_23901 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (274902 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23901_aux.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23901_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
