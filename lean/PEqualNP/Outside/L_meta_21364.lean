import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21364

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [5, 7]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [14, 6]⟩,
    ⟨.and, [2, 15]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 17]⟩], 20⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21364

open PEqualNP.Outside.L_meta_21364 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21364 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40410 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
