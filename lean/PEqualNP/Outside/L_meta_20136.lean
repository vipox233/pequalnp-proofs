import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20136 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17022383772369540555 : ℕ).testBit (8 * u.val + v.val)) 34) := by
  refine ⟨⟨[⟨.or, [0, 13]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [23, 20]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [25, 18]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [29, 6]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [31, 12]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [34, 12]⟩, ⟨.or, [35, 14]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [38, 15]⟩, ⟨.and, [22, 24]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [30, 32]⟩, ⟨.and, [33, 36]⟩, ⟨.and, [37, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [45, 42]⟩, ⟨.or, [46, 43]⟩, ⟨.or, [47, 44]⟩], 48⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
