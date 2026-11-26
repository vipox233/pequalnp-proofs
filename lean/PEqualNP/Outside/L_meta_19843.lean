import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19843_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 11]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [8, 19]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [24, 18]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [27, 19]⟩,
    ⟨.and, [2, 28]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [30, 15]⟩,
    ⟨.or, [31, 18]⟩,
    ⟨.and, [3, 32]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.and, [4, 34]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [36, 15]⟩,
    ⟨.or, [37, 17]⟩,
    ⟨.and, [5, 38]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [6, 40]⟩,
    ⟨.or, [18, 21]⟩,
    ⟨.and, [7, 42]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [44, 29]⟩,
    ⟨.or, [45, 33]⟩,
    ⟨.or, [46, 35]⟩,
    ⟨.or, [47, 39]⟩,
    ⟨.or, [48, 41]⟩,
    ⟨.or, [49, 43]⟩], 50⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19843_aux

theorem PEqualNP.Outside.L_meta_19843 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8465338603409387505 : ℕ).testBit (8 * u.val + v.val)) 35 := by
  exact ⟨PEqualNP.Outside.L_meta_19843_aux.circuit, PEqualNP.Outside.L_meta_19843_aux.mono,
    by decide, by decide +kernel⟩
