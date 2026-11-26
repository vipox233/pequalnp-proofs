import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19855_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 15]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [22, 16]⟩,
    ⟨.and, [1, 23]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [25, 12]⟩,
    ⟨.or, [26, 13]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [29, 16]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [34, 17]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [39, 18]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [21, 24]⟩,
    ⟨.or, [42, 28]⟩,
    ⟨.or, [43, 31]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 36]⟩,
    ⟨.or, [46, 38]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19855_aux

theorem PEqualNP.Outside.L_meta_19855 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10192891319453729625 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19855_aux.circuit, PEqualNP.Outside.L_meta_19855_aux.mono,
    by decide, by decide +kernel⟩
