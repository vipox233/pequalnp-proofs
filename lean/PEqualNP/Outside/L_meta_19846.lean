import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19846_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 12]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.and, [0, 19]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [21, 15]⟩,
    ⟨.and, [1, 22]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.and, [2, 24]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [3, 26]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.and, [4, 28]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [30, 14]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.and, [7, 35]⟩,
    ⟨.or, [20, 23]⟩,
    ⟨.or, [37, 25]⟩,
    ⟨.or, [38, 27]⟩,
    ⟨.or, [39, 29]⟩,
    ⟨.or, [40, 32]⟩,
    ⟨.or, [41, 34]⟩,
    ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19846_aux

theorem PEqualNP.Outside.L_meta_19846 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10108984885455782700 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.L_meta_19846_aux.circuit, PEqualNP.Outside.L_meta_19846_aux.mono,
    by decide, by decide +kernel⟩
