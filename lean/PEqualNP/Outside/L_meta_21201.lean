import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21201_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [3, 15]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [14, 17]⟩], 18⟩

theorem fan : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_21201_aux

theorem PEqualNP.Outside.L_meta_21201 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (106364 : ℕ).testBit (5 * u.val + v.val)) 10 := by
  exact ⟨PEqualNP.Outside.L_meta_21201_aux.circuit, PEqualNP.Outside.L_meta_21201_aux.fan, by decide, by decide +kernel⟩
