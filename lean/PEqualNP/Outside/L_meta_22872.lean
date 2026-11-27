import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22872 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883510 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  let C : Circuit := ⟨[⟨.or, [2, 6]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [1, 15]⟩, ⟨.and, [18, 17]⟩, ⟨.and, [16, 19]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [23, 22]⟩], 24⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
