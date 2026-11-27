import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25202
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.or, [1, 0]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.or, [8, 6]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [4, 0]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.and, [12, 10]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [14, 9]⟩], 15⟩

end PEqualNP.Outside.L_meta_25202

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_25202 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33713 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_25202.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_25202.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
