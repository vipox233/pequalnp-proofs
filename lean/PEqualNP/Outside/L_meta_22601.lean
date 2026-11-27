import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22601
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 0]⟩,
    ⟨.or, [2, 0]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [14, 2]⟩,
    ⟨.or, [14, 5]⟩,
    ⟨.and, [16, 11]⟩,
    ⟨.or, [4, 17]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [3, 19]⟩,
    ⟨.and, [20, 13]⟩,
    ⟨.or, [21, 18]⟩], 22⟩

end PEqualNP.Outside.L_meta_22601

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_22601 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965691 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_22601.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22601.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
