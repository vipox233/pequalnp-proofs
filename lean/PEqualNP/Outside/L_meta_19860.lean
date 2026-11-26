import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19860_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.or, [9, 18]⟩,
    ⟨.or, [22, 19]⟩,
    ⟨.and, [0, 23]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [27, 19]⟩,
    ⟨.and, [2, 28]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [30, 13]⟩,
    ⟨.or, [31, 17]⟩,
    ⟨.and, [3, 32]⟩,
    ⟨.or, [10, 21]⟩,
    ⟨.and, [4, 34]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [40, 19]⟩,
    ⟨.and, [7, 41]⟩,
    ⟨.or, [24, 26]⟩,
    ⟨.or, [43, 29]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 35]⟩,
    ⟨.or, [46, 37]⟩,
    ⟨.or, [47, 39]⟩,
    ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19860_aux

theorem PEqualNP.Outside.L_meta_19860 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12940930042358455530 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19860_aux.circuit, PEqualNP.Outside.L_meta_19860_aux.mono,
    by decide, by decide +kernel⟩
