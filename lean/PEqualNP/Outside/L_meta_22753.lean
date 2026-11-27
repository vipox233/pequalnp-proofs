import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22753
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [0, 7]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [6, 15]⟩,
    ⟨.or, [4, 13]⟩,
    ⟨.and, [14, 17]⟩,
    ⟨.and, [16, 18]⟩,
    ⟨.and, [11, 10]⟩,
    ⟨.or, [19, 20]⟩,
    ⟨.or, [22, 21]⟩], 23⟩

end PEqualNP.Outside.L_meta_22753

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_22753 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940151 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  refine ⟨PEqualNP.Outside.L_meta_22753.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22753.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
