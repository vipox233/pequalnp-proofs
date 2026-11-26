import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21388

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [8, 6]⟩,
    ⟨.or, [4, 9]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [7, 6]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.or, [3, 1]⟩,
    ⟨.and, [15, 16]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [11, 18]⟩], 19⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21388

open PEqualNP.Outside.L_meta_21388 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21388 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (111093 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
