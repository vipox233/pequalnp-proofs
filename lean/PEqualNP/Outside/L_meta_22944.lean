import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22944

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [2, 7]⟩,
    ⟨.or, [1, 6]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [13, 3]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [0, 15]⟩,
    ⟨.or, [11, 10]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [3, 18]⟩,
    ⟨.or, [0, 19]⟩,
    ⟨.and, [17, 20]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.or, [14, 22]⟩,
    ⟨.or, [12, 23]⟩], 24⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22944

open PEqualNP.Outside.L_meta_22944 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_22944 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4028156 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
