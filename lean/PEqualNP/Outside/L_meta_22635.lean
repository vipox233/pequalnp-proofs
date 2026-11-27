import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22635_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [7, 8]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [6, 11]⟩,
    ⟨.or, [9, 12]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [4, 10]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [1, 15]⟩,
    ⟨.and, [3, 16]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [19, 21]⟩,
    ⟨.or, [20, 22]⟩], 23⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_22635_aux

theorem PEqualNP.Outside.L_meta_22635 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (808574 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact ⟨PEqualNP.Outside.L_meta_22635_aux.circuit, PEqualNP.Outside.L_meta_22635_aux.mono, by decide, by decide +kernel⟩
