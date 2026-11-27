import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_22952 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908215 : ℕ).testBit (6 * u.val + v.val)) 16 := by
  let C : Circuit := ⟨[⟨.or, [5, 9]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [5, 18]⟩, ⟨.and, [19, 11]⟩, ⟨.and, [12, 16]⟩, ⟨.and, [15, 17]⟩, ⟨.or, [20, 21]⟩, ⟨.or, [23, 22]⟩], 24⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
