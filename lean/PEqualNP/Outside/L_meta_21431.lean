import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21431

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.and, [4, 0]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [10, 7]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.or, [1, 0]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [6, 16]⟩,
    ⟨.and, [15, 17]⟩,
    ⟨.or, [14, 18]⟩,
    ⟨.or, [12, 19]⟩,
    ⟨.or, [9, 20]⟩], 21⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21431

open PEqualNP.Outside.L_meta_21431 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21431 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241565 : ℕ).testBit (5 * u.val + v.val)) 14 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
