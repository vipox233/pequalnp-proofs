import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20113 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3120634772845828080 : ℕ).testBit (8 * u.val + v.val)) 30) := by
  refine ⟨⟨[⟨.or, [0, 8]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [26, 8]⟩, ⟨.or, [27, 13]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [29, 10]⟩, ⟨.or, [30, 14]⟩, ⟨.or, [13, 17]⟩, ⟨.or, [32, 20]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [1, 22]⟩, ⟨.or, [5, 22]⟩, ⟨.and, [24, 25]⟩, ⟨.and, [28, 31]⟩, ⟨.and, [33, 34]⟩, ⟨.and, [35, 9]⟩, ⟨.and, [36, 11]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 41]⟩], 45⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
