import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24465
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [1, 0]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.and, [8, 7]⟩,
    ⟨.or, [5, 2]⟩,
    ⟨.and, [10, 6]⟩,
    ⟨.or, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_24465

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_24465 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (102204 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24465.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_24465.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
