import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25269
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.and, [3, 0]⟩,
    ⟨.or, [3, 2]⟩,
    ⟨.and, [7, 1]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.not, [9]⟩,
    ⟨.or, [10, 1]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.not, [12]⟩,
    ⟨.or, [13, 0]⟩,
    ⟨.and, [11, 14]⟩], 15⟩

end PEqualNP.Outside.L_meta_25269

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_25269 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147495 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25269.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_25269.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
