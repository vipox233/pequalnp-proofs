import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21252

open PEqualNP.CircuitLowerBounds

private def circuit : Circuit :=
  ⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.or, [1, 10]⟩,
    ⟨.or, [8, 7]⟩,
    ⟨.or, [5, 12]⟩,
    ⟨.or, [3, 13]⟩,
    ⟨.or, [1, 14]⟩,
    ⟨.and, [9, 15]⟩,
    ⟨.or, [6, 16]⟩,
    ⟨.or, [2, 17]⟩,
    ⟨.and, [11, 18]⟩], 19⟩

private theorem monotone : PEqualNP.MetaComplexity.Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21252

open PEqualNP.Outside.L_meta_21252 in
set_option maxRecDepth 4000 in
set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.L_meta_21252 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36030 : ℕ).testBit (5 * u.val + v.val)) 11 := by
  exact ⟨circuit, monotone, by decide, by decide +kernel⟩
