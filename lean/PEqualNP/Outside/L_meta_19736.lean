import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19736

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [10, 15]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [11, 19]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.or, [10, 22]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [8, 22]⟩,
    ⟨.or, [12, 20]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [21, 29]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [15, 31]⟩,
    ⟨.or, [18, 32]⟩,
    ⟨.and, [0, 23]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.and, [2, 25]⟩,
    ⟨.and, [3, 26]⟩,
    ⟨.and, [4, 27]⟩,
    ⟨.and, [5, 28]⟩,
    ⟨.and, [6, 30]⟩,
    ⟨.and, [7, 33]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [36, 42]⟩,
    ⟨.or, [37, 43]⟩,
    ⟨.or, [38, 44]⟩,
    ⟨.or, [39, 45]⟩,
    ⟨.or, [40, 46]⟩,
    ⟨.or, [41, 47]⟩], 48⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19736

open PEqualNP.Outside.L_meta_19736 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_19736 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12374965280498343630 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
