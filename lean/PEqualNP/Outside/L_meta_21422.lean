import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21422

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.and, [4, 2]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [8, 6]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [7, 6]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.or, [1, 14]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.or, [2, 16]⟩,
    ⟨.or, [0, 17]⟩,
    ⟨.and, [15, 18]⟩,
    ⟨.or, [12, 19]⟩,
    ⟨.or, [9, 20]⟩], 21⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21422

open PEqualNP.Outside.L_meta_21422 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21422 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (112380 : ℕ).testBit (5 * u.val + v.val)) 13 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
