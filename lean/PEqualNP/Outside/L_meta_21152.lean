import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21152

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [1, 5]⟩,
    ⟨.or, [9, 3]⟩,
    ⟨.or, [4, 0]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [9, 6]⟩,
    ⟨.or, [0, 13]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [2, 15]⟩,
    ⟨.and, [14, 16]⟩,
    ⟨.or, [12, 17]⟩], 18⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21152

open PEqualNP.Outside.L_meta_21152 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21152 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39738 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
