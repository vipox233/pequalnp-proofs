import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22769_aux

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [8, 7]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.and, [14, 15]⟩,
    ⟨.or, [9, 7]⟩,
    ⟨.and, [0, 17]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [12, 13]⟩,
    ⟨.or, [4, 20]⟩,
    ⟨.or, [19, 21]⟩], 22⟩

end PEqualNP.Outside.L_meta_22769_aux

theorem PEqualNP.Outside.L_meta_22769 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1947503 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  exact ⟨PEqualNP.Outside.L_meta_22769_aux.circuit,
    by
      intro gate hgate
      simp only [PEqualNP.Outside.L_meta_22769_aux.circuit, List.mem_cons, List.not_mem_nil, or_false] at hgate
      rcases hgate with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp,
    by decide +kernel, by decide +kernel⟩
