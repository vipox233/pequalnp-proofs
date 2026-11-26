import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20346 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8280023251922031930 : ℕ).testBit (8 * u.val + v.val)) 26) := by
  refine ⟨⟨[⟨.or, [11, 3]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [8, 19]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [0, 25]⟩, ⟨.or, [24, 9]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [0, 19]⟩, ⟨.or, [26, 20]⟩, ⟨.and, [30, 28]⟩, ⟨.or, [1, 14]⟩, ⟨.and, [29, 16]⟩, ⟨.and, [23, 27]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [32, 34]⟩, ⟨.and, [38, 37]⟩, ⟨.or, [31, 33]⟩, ⟨.or, [39, 40]⟩], 41⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
