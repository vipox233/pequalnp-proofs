import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22502
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [3, 7]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [6, 12]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [16, 17]⟩,
    ⟨.and, [15, 13]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [20, 18]⟩,
    ⟨.or, [21, 19]⟩], 22⟩

end PEqualNP.Outside.L_meta_22502

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_22502 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898090 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_22502.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22502.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
