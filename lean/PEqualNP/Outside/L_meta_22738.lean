import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22738

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.or, [12, 9]⟩,
    ⟨.and, [11, 13]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.and, [16, 5]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.and, [18, 6]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [20, 17]⟩,
    ⟨.or, [21, 19]⟩,
    ⟨.or, [22, 4]⟩], 23⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22738

open PEqualNP.Outside.L_meta_22738 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_22738 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1900285 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
