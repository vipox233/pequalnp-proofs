import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22939

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [5, 11]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [16, 8]⟩,
    ⟨.and, [2, 17]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.and, [3, 19]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [21, 18]⟩,
    ⟨.or, [22, 20]⟩,
    ⟨.or, [23, 4]⟩], 24⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22939

open PEqualNP.Outside.L_meta_22939 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_22939 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948669 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
