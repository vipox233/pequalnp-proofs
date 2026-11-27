import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23230
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [2, 1]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.not, [7]⟩,
    ⟨.or, [8, 0]⟩,
    ⟨.or, [7, 6]⟩,
    ⟨.and, [10, 9]⟩], 11⟩

end PEqualNP.Outside.L_meta_23230

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_23230 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50102 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23230.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23230.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
