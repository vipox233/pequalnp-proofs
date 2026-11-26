import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20065_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 12]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [3, 21]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [6, 20]⟩,
    ⟨.or, [3, 5]⟩,
    ⟨.or, [5, 7]⟩,
    ⟨.or, [26, 23]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [28, 25]⟩,
    ⟨.or, [22, 23]⟩,
    ⟨.or, [24, 25]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.or, [21, 24]⟩,
    ⟨.and, [16, 27]⟩,
    ⟨.and, [17, 29]⟩,
    ⟨.and, [18, 1]⟩,
    ⟨.and, [10, 30]⟩,
    ⟨.and, [11, 31]⟩,
    ⟨.and, [19, 0]⟩,
    ⟨.and, [14, 32]⟩,
    ⟨.and, [15, 33]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [42, 36]⟩,
    ⟨.or, [43, 37]⟩,
    ⟨.or, [44, 38]⟩,
    ⟨.or, [45, 39]⟩,
    ⟨.or, [46, 40]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_20065_aux

theorem PEqualNP.Outside.L_meta_20065 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15680755338451602420 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_20065_aux.circuit, PEqualNP.Outside.L_meta_20065_aux.mono,
    by decide, by decide +kernel⟩
