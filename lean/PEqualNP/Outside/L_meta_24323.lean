import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24323
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [2, 1]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.and, [4, 7]⟩,
    ⟨.or, [8, 0]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.and, [10, 6]⟩,
    ⟨.or, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_24323

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_24323 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4427327 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24323.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_24323.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
