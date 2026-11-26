import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19813_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [14, 16]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [22, 19]⟩,
    ⟨.and, [0, 23]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [29, 21]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [32, 21]⟩,
    ⟨.and, [4, 33]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [39, 20]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [24, 26]⟩,
    ⟨.or, [42, 28]⟩,
    ⟨.or, [43, 31]⟩,
    ⟨.or, [44, 34]⟩,
    ⟨.or, [45, 36]⟩,
    ⟨.or, [46, 38]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19813_aux

theorem PEqualNP.Outside.L_meta_19813 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6614477138885590260 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19813_aux.circuit, PEqualNP.Outside.L_meta_19813_aux.mono,
    by decide, by decide +kernel⟩
