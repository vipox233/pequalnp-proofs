import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19865 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (973668958787351700 : ℕ).testBit (8 * u.val + v.val)) 29) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [9, 15]⟩,
      ⟨.or, [10, 12]⟩,
      ⟨.or, [15, 17]⟩,
      ⟨.and, [0, 18]⟩,
      ⟨.or, [13, 17]⟩,
      ⟨.and, [1, 20]⟩,
      ⟨.or, [11, 12]⟩,
      ⟨.or, [22, 14]⟩,
      ⟨.and, [2, 23]⟩,
      ⟨.or, [8, 13]⟩,
      ⟨.or, [25, 14]⟩,
      ⟨.and, [3, 26]⟩,
      ⟨.or, [14, 16]⟩,
      ⟨.and, [4, 28]⟩,
      ⟨.or, [9, 11]⟩,
      ⟨.or, [30, 13]⟩,
      ⟨.and, [5, 31]⟩,
      ⟨.or, [8, 16]⟩,
      ⟨.and, [6, 33]⟩,
      ⟨.or, [8, 10]⟩,
      ⟨.or, [35, 11]⟩,
      ⟨.and, [7, 36]⟩,
      ⟨.or, [19, 21]⟩,
      ⟨.or, [38, 24]⟩,
      ⟨.or, [39, 27]⟩,
      ⟨.or, [40, 29]⟩,
      ⟨.or, [41, 32]⟩,
      ⟨.or, [42, 34]⟩,
      ⟨.or, [43, 37]⟩], 44⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
