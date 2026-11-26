import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19814_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [9, 11]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.and, [0, 19]⟩,
    ⟨.or, [8, 18]⟩,
    ⟨.and, [1, 21]⟩,
    ⟨.or, [8, 16]⟩,
    ⟨.and, [2, 23]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.and, [3, 25]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.and, [4, 27]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [29, 15]⟩,
    ⟨.and, [5, 30]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.and, [6, 32]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [34, 14]⟩,
    ⟨.and, [7, 35]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.or, [37, 24]⟩,
    ⟨.or, [38, 26]⟩,
    ⟨.or, [39, 28]⟩,
    ⟨.or, [40, 31]⟩,
    ⟨.or, [41, 33]⟩,
    ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19814_aux

theorem PEqualNP.Outside.L_meta_19814 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7093347072485314830 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.L_meta_19814_aux.circuit, PEqualNP.Outside.L_meta_19814_aux.mono,
    by decide, by decide +kernel⟩
