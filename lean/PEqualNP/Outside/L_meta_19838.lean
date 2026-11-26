import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19838_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 11]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.and, [0, 19]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [1, 21]⟩,
    ⟨.or, [8, 12]⟩,
    ⟨.or, [23, 14]⟩,
    ⟨.and, [2, 24]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [26, 14]⟩,
    ⟨.and, [3, 27]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.and, [5, 31]⟩,
    ⟨.or, [14, 18]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.and, [7, 35]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.or, [37, 25]⟩,
    ⟨.or, [38, 28]⟩,
    ⟨.or, [39, 30]⟩,
    ⟨.or, [40, 32]⟩,
    ⟨.or, [41, 34]⟩,
    ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19838_aux

theorem PEqualNP.Outside.L_meta_19838 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.L_meta_19838_aux.circuit, PEqualNP.Outside.L_meta_19838_aux.mono,
    by decide, by decide +kernel⟩
