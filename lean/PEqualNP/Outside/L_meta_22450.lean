import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22450

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [6, 8]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [3, 17]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [19, 16]⟩,
    ⟨.or, [20, 18]⟩,
    ⟨.or, [21, 4]⟩], 22⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22450

open PEqualNP.Outside.L_meta_22450 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_22450 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1882101 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
