import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21395

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.and, [4, 2]⟩,
    ⟨.and, [8, 0]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.or, [3, 1]⟩,
    ⟨.and, [11, 12]⟩,
    ⟨.or, [7, 6]⟩,
    ⟨.or, [2, 1]⟩,
    ⟨.or, [0, 15]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [10, 18]⟩,
    ⟨.or, [9, 19]⟩], 20⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21395

open PEqualNP.Outside.L_meta_21395 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21395 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112124 : ℕ).testBit (5 * u.val + v.val)) 12 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
