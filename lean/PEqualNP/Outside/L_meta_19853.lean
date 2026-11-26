import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19853_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [10, 12]⟩,
    ⟨.or, [8, 11]⟩,
    ⟨.or, [8, 14]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [0, 20]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [22, 11]⟩,
    ⟨.or, [23, 14]⟩,
    ⟨.and, [1, 24]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [26, 18]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [29, 19]⟩,
    ⟨.and, [3, 30]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [32, 16]⟩,
    ⟨.and, [4, 33]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [35, 17]⟩,
    ⟨.and, [5, 36]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [38, 16]⟩,
    ⟨.and, [6, 39]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [7, 41]⟩,
    ⟨.or, [21, 25]⟩,
    ⟨.or, [43, 28]⟩,
    ⟨.or, [44, 31]⟩,
    ⟨.or, [45, 34]⟩,
    ⟨.or, [46, 37]⟩,
    ⟨.or, [47, 40]⟩,
    ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19853_aux

theorem PEqualNP.Outside.L_meta_19853 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3115533915564101205 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19853_aux.circuit, PEqualNP.Outside.L_meta_19853_aux.mono,
    by decide, by decide +kernel⟩
