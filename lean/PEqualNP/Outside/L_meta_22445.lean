import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22445 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881967 : ℕ).testBit (6 * u.val + v.val)) 13 := by
  let C : Circuit := ⟨[⟨.or, [7, 0]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [14, 1]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [5, 16]⟩, ⟨.or, [4, 15]⟩, ⟨.and, [19, 18]⟩, ⟨.or, [20, 21]⟩], 22⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
