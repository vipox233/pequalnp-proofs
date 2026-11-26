import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19859_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 13]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [20, 17]⟩,
    ⟨.and, [0, 21]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.and, [1, 23]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [25, 13]⟩,
    ⟨.or, [26, 14]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [31, 17]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [34, 16]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [37, 18]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [42, 28]⟩,
    ⟨.or, [43, 30]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 36]⟩,
    ⟨.or, [46, 39]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19859_aux

theorem PEqualNP.Outside.L_meta_19859 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3718182521909076510 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19859_aux.circuit, PEqualNP.Outside.L_meta_19859_aux.mono,
    by decide, by decide +kernel⟩
