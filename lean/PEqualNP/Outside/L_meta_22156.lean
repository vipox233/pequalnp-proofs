import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22156_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit :=
  ⟨[⟨.or, [1, 4]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [10, 12]⟩,
    ⟨.or, [13, 0]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [9, 8]⟩,
    ⟨.and, [16, 0]⟩,
    ⟨.or, [17, 15]⟩,
    ⟨.or, [18, 11]⟩,
    ⟨.or, [19, 3]⟩,
    ⟨.and, [14, 20]⟩], 21⟩

theorem h_mono : Monotone2 circ := by
  intro g hg
  simp only [circ, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem h_sz : circ.size ≤ 12 := by
  decide +kernel

theorem h_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (840636 : ℕ).testBit (6 * u.val + v.val)) circ := by
  decide +kernel

end PEqualNP.Outside.L_meta_22156_aux

theorem PEqualNP.Outside.L_meta_22156 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840636 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  exact ⟨PEqualNP.Outside.L_meta_22156_aux.circ, PEqualNP.Outside.L_meta_22156_aux.h_mono, PEqualNP.Outside.L_meta_22156_aux.h_sz, PEqualNP.Outside.L_meta_22156_aux.h_rep⟩
