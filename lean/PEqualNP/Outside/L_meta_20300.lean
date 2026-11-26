import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_20300 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8254449022188472170 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  let C : Circuit := ⟨[⟨.or, [0, 15]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [17, 24]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [29, 26]⟩, ⟨.or, [27, 29]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [32, 26]⟩, ⟨.or, [19, 23]⟩, ⟨.and, [25, 9]⟩, ⟨.or, [30, 22]⟩, ⟨.or, [33, 19]⟩, ⟨.and, [25, 31]⟩, ⟨.and, [36, 37]⟩, ⟨.and, [16, 34]⟩, ⟨.and, [21, 28]⟩, ⟨.or, [41, 38]⟩, ⟨.or, [39, 42]⟩, ⟨.or, [43, 40]⟩], 44⟩
  refine ⟨C, ?_, by decide, by decide⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
