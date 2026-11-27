import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24587
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [2, 1]⟩,
    ⟨.or, [6, 0]⟩,
    ⟨.and, [3, 6]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.and, [10, 9]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.not, [12]⟩], 13⟩

end PEqualNP.Outside.L_meta_24587

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_24587 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549391 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24587.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_24587.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
