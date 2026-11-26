import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19830_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 13]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [14, 17]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [26, 20]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [10, 21]⟩,
    ⟨.and, [5, 33]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.and, [6, 35]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [37, 18]⟩,
    ⟨.and, [7, 38]⟩,
    ⟨.or, [23, 25]⟩,
    ⟨.or, [40, 28]⟩,
    ⟨.or, [41, 30]⟩,
    ⟨.or, [42, 32]⟩,
    ⟨.or, [43, 34]⟩,
    ⟨.or, [44, 36]⟩,
    ⟨.or, [45, 39]⟩], 46⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19830_aux

theorem PEqualNP.Outside.L_meta_19830 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5582313321192137625 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  exact ⟨PEqualNP.Outside.L_meta_19830_aux.circuit, PEqualNP.Outside.L_meta_19830_aux.mono,
    by decide, by decide +kernel⟩
