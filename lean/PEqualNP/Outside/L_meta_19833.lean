import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19833_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [9, 21]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [12, 21]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [26, 15]⟩, ⟨.or, [27, 16]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [32, 18]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [35, 19]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [40, 18]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 31]⟩, ⟨.or, [45, 34]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

theorem mono : Monotone2 circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_19833_aux

theorem PEqualNP.Outside.L_meta_19833 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17604493529221135470 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  exact ⟨PEqualNP.Outside.L_meta_19833_aux.circuit, PEqualNP.Outside.L_meta_19833_aux.mono, by decide, by decide +kernel⟩
