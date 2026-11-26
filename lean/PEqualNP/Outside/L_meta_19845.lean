import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19845_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [22, 15]⟩,
    ⟨.or, [23, 19]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [26, 17]⟩,
    ⟨.and, [1, 27]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [2, 29]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [31, 19]⟩,
    ⟨.and, [3, 32]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.and, [4, 34]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [9, 18]⟩,
    ⟨.or, [40, 19]⟩,
    ⟨.and, [7, 41]⟩,
    ⟨.or, [25, 28]⟩,
    ⟨.or, [43, 30]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 35]⟩,
    ⟨.or, [46, 37]⟩,
    ⟨.or, [47, 39]⟩,
    ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19845_aux

theorem PEqualNP.Outside.L_meta_19845 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8572844398234278885 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19845_aux.circuit, PEqualNP.Outside.L_meta_19845_aux.mono,
    by decide, by decide +kernel⟩
