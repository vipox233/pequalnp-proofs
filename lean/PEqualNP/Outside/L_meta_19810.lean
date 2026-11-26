import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19810_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 13]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [20, 16]⟩,
    ⟨.and, [0, 21]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [23, 16]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [26, 19]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [33, 17]⟩,
    ⟨.and, [5, 34]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [36, 18]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [7, 39]⟩,
    ⟨.or, [22, 25]⟩,
    ⟨.or, [41, 28]⟩,
    ⟨.or, [42, 30]⟩,
    ⟨.or, [43, 32]⟩,
    ⟨.or, [44, 35]⟩,
    ⟨.or, [45, 38]⟩,
    ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19810_aux

theorem PEqualNP.Outside.L_meta_19810 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10184235645427475370 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_19810_aux.circuit, PEqualNP.Outside.L_meta_19810_aux.mono,
    by decide, by decide +kernel⟩
