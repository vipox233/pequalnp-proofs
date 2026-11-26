import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19848_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 10]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [8, 17]⟩,
    ⟨.or, [23, 18]⟩,
    ⟨.and, [0, 24]⟩,
    ⟨.or, [18, 20]⟩,
    ⟨.and, [1, 26]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [28, 19]⟩,
    ⟨.and, [2, 29]⟩,
    ⟨.or, [14, 22]⟩,
    ⟨.and, [3, 31]⟩,
    ⟨.or, [16, 21]⟩,
    ⟨.and, [4, 33]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [35, 20]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [10, 22]⟩,
    ⟨.and, [6, 38]⟩,
    ⟨.or, [17, 21]⟩,
    ⟨.and, [7, 40]⟩,
    ⟨.or, [25, 27]⟩,
    ⟨.or, [42, 30]⟩,
    ⟨.or, [43, 32]⟩,
    ⟨.or, [44, 34]⟩,
    ⟨.or, [45, 37]⟩,
    ⟨.or, [46, 39]⟩,
    ⟨.or, [47, 41]⟩], 48⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19848_aux

theorem PEqualNP.Outside.L_meta_19848 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16879102062354748875 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  exact ⟨PEqualNP.Outside.L_meta_19848_aux.circuit, PEqualNP.Outside.L_meta_19848_aux.mono,
    by decide, by decide +kernel⟩
