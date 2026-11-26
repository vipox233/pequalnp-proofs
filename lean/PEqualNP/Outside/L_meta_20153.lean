import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20153 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨⟨[⟨.or, [5, 6]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [26, 21]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [29, 8]⟩, ⟨.or, [30, 14]⟩, ⟨.or, [31, 19]⟩, ⟨.or, [32, 20]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [34, 14]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [36, 7]⟩, ⟨.or, [37, 8]⟩, ⟨.or, [38, 21]⟩, ⟨.and, [23, 24]⟩, ⟨.and, [25, 27]⟩, ⟨.and, [28, 33]⟩, ⟨.and, [35, 39]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [44, 42]⟩, ⟨.or, [45, 43]⟩], 46⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
