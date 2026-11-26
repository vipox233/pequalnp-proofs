import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22371

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [4, 11]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [3, 18]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [20, 17]⟩,
    ⟨.or, [21, 19]⟩], 22⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22371

open PEqualNP.Outside.L_meta_22371 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_22371 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841596 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
