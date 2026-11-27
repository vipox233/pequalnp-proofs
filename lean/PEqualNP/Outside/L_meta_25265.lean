import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25265
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [2, 0]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.or, [4, 0]⟩,
    ⟨.or, [4, 3]⟩,
    ⟨.and, [9, 1]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.and, [11, 7]⟩,
    ⟨.not, [12]⟩,
    ⟨.and, [13, 6]⟩,
    ⟨.or, [14, 10]⟩], 15⟩

end PEqualNP.Outside.L_meta_25265

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_25265 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (51001 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25265.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_25265.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
