import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19841_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 14]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.and, [0, 19]⟩,
    ⟨.or, [11, 17]⟩,
    ⟨.and, [1, 21]⟩,
    ⟨.or, [8, 18]⟩,
    ⟨.and, [2, 23]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [25, 15]⟩,
    ⟨.and, [3, 26]⟩,
    ⟨.or, [12, 17]⟩,
    ⟨.and, [4, 28]⟩,
    ⟨.or, [10, 18]⟩,
    ⟨.and, [5, 30]⟩,
    ⟨.or, [13, 14]⟩,
    ⟨.or, [32, 15]⟩,
    ⟨.and, [6, 33]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.and, [7, 35]⟩,
    ⟨.or, [20, 22]⟩,
    ⟨.or, [37, 24]⟩,
    ⟨.or, [38, 27]⟩,
    ⟨.or, [39, 29]⟩,
    ⟨.or, [40, 31]⟩,
    ⟨.or, [41, 34]⟩,
    ⟨.or, [42, 36]⟩], 43⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19841_aux

theorem PEqualNP.Outside.L_meta_19841 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5899763987308416705 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  exact ⟨PEqualNP.Outside.L_meta_19841_aux.circuit, PEqualNP.Outside.L_meta_19841_aux.mono,
    by decide, by decide +kernel⟩
