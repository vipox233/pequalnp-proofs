import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21211

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.and, [8, 0]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.or, [10, 0]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [14, 15]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [9, 17]⟩], 18⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21211

open PEqualNP.Outside.L_meta_21211 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21211 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114172 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
