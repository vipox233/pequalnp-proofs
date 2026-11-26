import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20156

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [8, 12]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [0, 20]⟩,
    ⟨.or, [7, 21]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [25, 26]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [22, 28]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.or, [21, 23]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [20, 24]⟩,
    ⟨.and, [16, 27]⟩,
    ⟨.and, [17, 29]⟩,
    ⟨.and, [4, 18]⟩,
    ⟨.and, [9, 30]⟩,
    ⟨.and, [11, 31]⟩,
    ⟨.and, [6, 19]⟩,
    ⟨.and, [14, 32]⟩,
    ⟨.and, [15, 33]⟩,
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

end PEqualNP.Outside.L_meta_20156

open PEqualNP.Outside.L_meta_20156 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_20156 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16643312522802600795 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
