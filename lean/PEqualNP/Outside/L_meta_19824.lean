import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19824_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 10]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [8, 18]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [23, 19]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.and, [1, 26]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [28, 17]⟩,
    ⟨.and, [2, 29]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.and, [3, 31]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [4, 33]⟩,
    ⟨.or, [10, 22]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [12, 22]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [39, 20]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [25, 27]⟩,
    ⟨.or, [42, 30]⟩,
    ⟨.or, [43, 32]⟩,
    ⟨.or, [44, 34]⟩,
    ⟨.or, [45, 36]⟩,
    ⟨.or, [46, 38]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19824_aux

theorem PEqualNP.Outside.L_meta_19824 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8347929566805686415 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19824_aux.circuit, PEqualNP.Outside.L_meta_19824_aux.mono,
    by decide, by decide +kernel⟩
