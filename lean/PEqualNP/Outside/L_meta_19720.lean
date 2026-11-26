import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19720_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 14]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [12, 18]⟩,
    ⟨.or, [10, 20]⟩,
    ⟨.and, [0, 21]⟩,
    ⟨.or, [11, 19]⟩,
    ⟨.and, [1, 23]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [25, 16]⟩,
    ⟨.and, [2, 26]⟩,
    ⟨.or, [8, 19]⟩,
    ⟨.and, [3, 28]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [30, 17]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [33, 16]⟩,
    ⟨.and, [5, 34]⟩,
    ⟨.or, [9, 20]⟩,
    ⟨.and, [6, 36]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [7, 38]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [40, 27]⟩,
    ⟨.or, [41, 29]⟩,
    ⟨.or, [42, 32]⟩,
    ⟨.or, [43, 35]⟩,
    ⟨.or, [44, 37]⟩,
    ⟨.or, [45, 39]⟩], 46⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19720_aux

theorem PEqualNP.Outside.L_meta_19720 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7582498071666593340 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  exact ⟨PEqualNP.Outside.L_meta_19720_aux.circuit, PEqualNP.Outside.L_meta_19720_aux.mono,
    by decide, by decide +kernel⟩
