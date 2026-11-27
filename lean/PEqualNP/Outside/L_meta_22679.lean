import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22679

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [4, 5]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [16, 7]⟩,
    ⟨.and, [2, 17]⟩,
    ⟨.and, [3, 10]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [20, 18]⟩,
    ⟨.or, [21, 19]⟩], 22⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22679

open PEqualNP.Outside.L_meta_22679 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_22679 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843063 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
