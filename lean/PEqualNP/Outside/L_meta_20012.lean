import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20012
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [4, 14]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [5, 17]⟩,
    ⟨.or, [0, 8]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [3, 10]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [2, 7]⟩,
    ⟨.or, [1, 23]⟩,
    ⟨.or, [6, 24]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [10, 20]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [1, 25]⟩,
    ⟨.or, [28, 29]⟩,
    ⟨.or, [14, 22]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [18, 26]⟩,
    ⟨.or, [19, 27]⟩,
    ⟨.and, [21, 30]⟩,
    ⟨.and, [37, 38]⟩,
    ⟨.and, [36, 35]⟩,
    ⟨.and, [33, 32]⟩,
    ⟨.and, [31, 34]⟩,
    ⟨.or, [40, 42]⟩,
    ⟨.or, [39, 43]⟩,
    ⟨.or, [45, 44]⟩,
    ⟨.or, [46, 41]⟩], 47⟩

end PEqualNP.Outside.L_meta_20012

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_20012 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176519996038833020 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  refine ⟨PEqualNP.Outside.L_meta_20012.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_20012.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
