import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24850
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit := ⟨[⟨.not, [4]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.or, [3, 1]⟩,
    ⟨.and, [8, 2]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [12, 0]⟩,
    ⟨.and, [10, 13]⟩], 14⟩

end PEqualNP.Outside.L_meta_24850

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_24850 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2180783 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨PEqualNP.Outside.L_meta_24850.witness, ?_, by decide, ?_⟩
  · intro g h
    simp only [PEqualNP.Outside.L_meta_24850.witness, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
