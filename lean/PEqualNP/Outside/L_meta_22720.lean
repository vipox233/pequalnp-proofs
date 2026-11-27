import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22720_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  ⟨[⟨.or, [6, 2]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [5, 0]⟩,
    ⟨.or, [11, 10]⟩,
    ⟨.or, [9, 13]⟩,
    ⟨.or, [13, 0]⟩,
    ⟨.and, [11, 10]⟩,
    ⟨.and, [14, 12]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.or, [4, 1]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.and, [20, 19]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [22, 21]⟩], 23⟩

theorem h_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem h_sz : circ.size ≤ 14 := by
  decide +kernel

theorem h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1881901 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22720_aux

theorem PEqualNP.Outside.L_meta_22720 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881901 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22720_aux.circ, PEqualNP.Outside.L_meta_22720_aux.h_mono, PEqualNP.Outside.L_meta_22720_aux.h_sz, PEqualNP.Outside.L_meta_22720_aux.h_rep⟩
