import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19840_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [14, 18]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [24, 18]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [27, 19]⟩,
    ⟨.and, [2, 28]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [30, 13]⟩,
    ⟨.or, [31, 19]⟩,
    ⟨.and, [3, 32]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [4, 34]⟩,
    ⟨.or, [18, 21]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [16, 20]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [11, 16]⟩,
    ⟨.or, [40, 19]⟩,
    ⟨.and, [7, 41]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [43, 29]⟩,
    ⟨.or, [44, 33]⟩,
    ⟨.or, [45, 35]⟩,
    ⟨.or, [46, 37]⟩,
    ⟨.or, [47, 39]⟩,
    ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19840_aux

theorem PEqualNP.Outside.L_meta_19840 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14802692711996862330 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19840_aux.circuit, PEqualNP.Outside.L_meta_19840_aux.mono,
    by decide, by decide +kernel⟩
