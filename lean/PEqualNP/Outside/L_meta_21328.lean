import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21328

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [1, 6]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.or, [0, 10]⟩,
    ⟨.or, [5, 0]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [7, 15]⟩,
    ⟨.or, [2, 16]⟩,
    ⟨.and, [11, 17]⟩,
    ⟨.or, [4, 18]⟩], 19⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21328

open PEqualNP.Outside.L_meta_21328 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21328 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105853 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
