import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22674
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [6, 7]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.and, [1, 16]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [21, 22]⟩], 23⟩

end PEqualNP.Outside.L_meta_22674

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_22674 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841661 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  refine ⟨PEqualNP.Outside.L_meta_22674.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22674.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
