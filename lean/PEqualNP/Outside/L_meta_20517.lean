import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20517

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.and, [13, 14]⟩], 15⟩

theorem mono : Monotone2 witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem small : witness.size ≤ 8 := by decide

set_option maxRecDepth 100000 in
theorem rep : Represents (fun (u : Fin 3) (v : Fin 5) => (3502 : ℕ).testBit (5 * u.val + v.val)) witness := by
  decide +kernel

end PEqualNP.Outside.L_meta_20517

theorem PEqualNP.Outside.L_meta_20517 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 5) => (3502 : ℕ).testBit (5 * u.val + v.val)) 8) :=
  ⟨PEqualNP.Outside.L_meta_20517.witness, PEqualNP.Outside.L_meta_20517.mono, PEqualNP.Outside.L_meta_20517.small, PEqualNP.Outside.L_meta_20517.rep⟩
