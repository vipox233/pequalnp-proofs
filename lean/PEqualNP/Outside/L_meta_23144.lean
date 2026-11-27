import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_23144 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (14141 : ℕ).testBit (6 * u.val + v.val)) 10 := by
  let C : Circuit := ⟨[⟨.or, [5, 6]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [15, 14]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [16, 17]⟩], 18⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
