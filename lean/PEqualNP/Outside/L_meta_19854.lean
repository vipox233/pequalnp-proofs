import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19854_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 15]⟩,
    ⟨.or, [10, 14]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [21, 17]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [24, 20]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [16, 19]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [17, 20]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [9, 17]⟩,
    ⟨.or, [33, 18]⟩,
    ⟨.and, [5, 34]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [36, 10]⟩,
    ⟨.or, [37, 12]⟩,
    ⟨.or, [38, 13]⟩,
    ⟨.and, [6, 39]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [41, 19]⟩,
    ⟨.and, [7, 42]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [44, 28]⟩,
    ⟨.or, [45, 30]⟩,
    ⟨.or, [46, 32]⟩,
    ⟨.or, [47, 35]⟩,
    ⟨.or, [48, 40]⟩,
    ⟨.or, [49, 43]⟩], 50⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19854_aux

theorem PEqualNP.Outside.L_meta_19854 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13418315418863193045 : ℕ).testBit (8 * u.val + v.val)) 35 := by
  exact ⟨PEqualNP.Outside.L_meta_19854_aux.circuit, PEqualNP.Outside.L_meta_19854_aux.mono,
    by decide, by decide +kernel⟩
