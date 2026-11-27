import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22736 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899642 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  let C : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [6, 17]⟩, ⟨.and, [18, 15]⟩, ⟨.and, [14, 16]⟩, ⟨.or, [19, 20]⟩], 21⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
