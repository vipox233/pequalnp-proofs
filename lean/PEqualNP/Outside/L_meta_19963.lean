import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19963 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1110766810026783180 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨⟨[
    ⟨.or, [4, 7]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [0, 5]⟩,
    ⟨.or, [7, 19]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.or, [1, 21]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [9, 14]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [10, 28]⟩,
    ⟨.or, [11, 27]⟩,
    ⟨.or, [13, 30]⟩,
    ⟨.or, [8, 27]⟩,
    ⟨.or, [12, 32]⟩,
    ⟨.and, [16, 29]⟩,
    ⟨.and, [22, 25]⟩,
    ⟨.and, [20, 26]⟩,
    ⟨.and, [6, 31]⟩,
    ⟨.and, [3, 33]⟩,
    ⟨.and, [18, 23]⟩,
    ⟨.and, [17, 24]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [41, 36]⟩,
    ⟨.or, [42, 37]⟩,
    ⟨.or, [43, 38]⟩,
    ⟨.or, [44, 39]⟩,
    ⟨.or, [45, 40]⟩
  ], 46⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
