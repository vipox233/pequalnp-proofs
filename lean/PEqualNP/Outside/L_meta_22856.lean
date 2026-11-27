import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22856 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1881470 : ℕ).testBit (6 * u.val + v.val)) 15 := by
  let C : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [18, 16]⟩, ⟨.and, [17, 15]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [22, 21]⟩], 23⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
