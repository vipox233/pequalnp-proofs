import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24817
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.and, [1, 0]⟩,
    ⟨.or, [1, 0]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [9, 12]⟩,
    ⟨.or, [13, 10]⟩], 14⟩

end PEqualNP.Outside.L_meta_24817

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_24817 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148126 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24817.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_24817.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
