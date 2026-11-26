import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20306

open PEqualNP.CircuitLowerBounds

-- The circuit from PR #27136 is transported by relabelling the two vertex sets.
private def circuit : Circuit :=
  ⟨[
    ⟨.or, [2, 10]⟩,
    ⟨.or, [3, 15]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [17, 12]⟩,
    ⟨.or, [14, 1]⟩,
    ⟨.or, [11, 7]⟩,
    ⟨.or, [5, 13]⟩,
    ⟨.or, [18, 13]⟩,
    ⟨.or, [21, 22]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.or, [2, 22]⟩,
    ⟨.or, [19, 21]⟩,
    ⟨.or, [17, 16]⟩,
    ⟨.and, [24, 25]⟩,
    ⟨.and, [19, 26]⟩,
    ⟨.or, [25, 24]⟩,
    ⟨.or, [23, 12]⟩,
    ⟨.or, [10, 29]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.and, [31, 34]⟩,
    ⟨.and, [32, 28]⟩,
    ⟨.or, [27, 20]⟩,
    ⟨.or, [0, 33]⟩,
    ⟨.and, [37, 38]⟩,
    ⟨.or, [39, 30]⟩,
    ⟨.or, [35, 40]⟩,
    ⟨.or, [41, 36]⟩], 42⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20306

open PEqualNP.Outside.L_meta_20306 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_20306 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5145875557475495640 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
