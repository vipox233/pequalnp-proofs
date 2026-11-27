import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22606
open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.and, [0, 16]⟩,
    ⟨.and, [13, 11]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.or, [21, 14]⟩], 22⟩

end PEqualNP.Outside.L_meta_22606

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem PEqualNP.Outside.L_meta_22606 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4028411 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_22606.circuit, ?_, by decide +kernel, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_22606.circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
