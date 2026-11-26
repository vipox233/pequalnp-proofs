import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19844_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [11, 19]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [22, 16]⟩,
    ⟨.and, [1, 23]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [2, 25]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [27, 18]⟩,
    ⟨.and, [3, 28]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [30, 17]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [33, 13]⟩,
    ⟨.or, [34, 15]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [37, 16]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [12, 19]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [21, 24]⟩,
    ⟨.or, [42, 26]⟩,
    ⟨.or, [43, 29]⟩,
    ⟨.or, [44, 32]⟩,
    ⟨.or, [45, 36]⟩,
    ⟨.or, [46, 39]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19844_aux

theorem PEqualNP.Outside.L_meta_19844 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8254449022188472170 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19844_aux.circuit, PEqualNP.Outside.L_meta_19844_aux.mono,
    by decide, by decide +kernel⟩
