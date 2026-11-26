import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_19732 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8109965352779728530 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  let C : Circuit := ⟨[⟨.or, [3, 10]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [2, 18]⟩, ⟨.or, [23, 5]⟩, ⟨.and, [17, 20]⟩, ⟨.or, [23, 22]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [25, 15]⟩, ⟨.and, [19, 27]⟩, ⟨.or, [2, 26]⟩, ⟨.or, [23, 23]⟩, ⟨.or, [28, 31]⟩, ⟨.or, [29, 12]⟩, ⟨.or, [34, 29]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [17, 36]⟩, ⟨.or, [18, 14]⟩, ⟨.and, [38, 35]⟩, ⟨.and, [33, 37]⟩, ⟨.or, [30, 39]⟩, ⟨.or, [21, 41]⟩, ⟨.or, [42, 40]⟩], 43⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
