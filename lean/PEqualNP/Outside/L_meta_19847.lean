import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19847_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 11]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [13, 16]⟩,
    ⟨.or, [13, 17]⟩,
    ⟨.or, [15, 18]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [12, 19]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.or, [8, 21]⟩,
    ⟨.and, [2, 26]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.and, [3, 28]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [30, 16]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [9, 19]⟩,
    ⟨.and, [5, 33]⟩,
    ⟨.or, [15, 20]⟩,
    ⟨.and, [6, 35]⟩,
    ⟨.or, [11, 21]⟩,
    ⟨.and, [7, 37]⟩,
    ⟨.or, [23, 25]⟩,
    ⟨.or, [39, 27]⟩,
    ⟨.or, [40, 29]⟩,
    ⟨.or, [41, 32]⟩,
    ⟨.or, [42, 34]⟩,
    ⟨.or, [43, 36]⟩,
    ⟨.or, [44, 38]⟩], 45⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19847_aux

theorem PEqualNP.Outside.L_meta_19847 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15611213044641773910 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  exact ⟨PEqualNP.Outside.L_meta_19847_aux.circuit, PEqualNP.Outside.L_meta_19847_aux.mono,
    by decide, by decide +kernel⟩
