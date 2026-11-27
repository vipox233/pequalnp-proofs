import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22509

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [7, 8]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [19, 17]⟩,
    ⟨.or, [20, 18]⟩,
    ⟨.or, [21, 4]⟩], 22⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22509

open PEqualNP.Outside.L_meta_22509 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_22509 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1898233 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
