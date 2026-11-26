import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20182 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3537932711340590220 : ℕ).testBit (8 * u.val + v.val)) 24) := by
  refine ⟨⟨[⟨.or, [7, 10]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [29, 20]⟩, ⟨.and, [21, 24]⟩, ⟨.and, [18, 25]⟩, ⟨.and, [19, 20]⟩, ⟨.and, [26, 27]⟩, ⟨.and, [28, 30]⟩, ⟨.or, [31, 32]⟩, ⟨.or, [36, 33]⟩, ⟨.or, [37, 34]⟩, ⟨.or, [38, 35]⟩], 39⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
