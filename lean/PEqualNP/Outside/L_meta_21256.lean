import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21256_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[
    ⟨.or, [6, 7]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 9]⟩,
    ⟨.and, [10, 11]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.and, [16, 15]⟩,
    ⟨.or, [12, 17]⟩
  ], 18⟩

theorem ok_gates : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21256_aux

theorem PEqualNP.Outside.L_meta_21256 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (36286 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  exact ⟨PEqualNP.Outside.L_meta_21256_aux.circuit, PEqualNP.Outside.L_meta_21256_aux.ok_gates, by decide, by decide +kernel⟩
