import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19866_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [20, 17]⟩,
    ⟨.and, [0, 21]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [1, 23]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [25, 18]⟩,
    ⟨.and, [2, 26]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [28, 19]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [31, 16]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [34, 18]⟩,
    ⟨.and, [5, 35]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [6, 37]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.and, [7, 39]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [41, 27]⟩,
    ⟨.or, [42, 30]⟩,
    ⟨.or, [43, 33]⟩,
    ⟨.or, [44, 36]⟩,
    ⟨.or, [45, 38]⟩,
    ⟨.or, [46, 40]⟩], 47⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19866_aux

theorem PEqualNP.Outside.L_meta_19866 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1125029453109683085 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_19866_aux.circuit, PEqualNP.Outside.L_meta_19866_aux.mono,
    by decide, by decide +kernel⟩
