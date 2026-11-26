import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20855 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (27007169 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  let C : Circuit := ⟨[⟨.or, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [16, 5]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [18, 17]⟩], 19⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
