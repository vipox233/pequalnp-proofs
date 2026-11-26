import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19832 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5918728716082980945 : ℕ).testBit (8 * u.val + v.val)) 27 := by
  refine ⟨⟨[⟨.or, [8, 9]⟩,
      ⟨.or, [10, 15]⟩,
      ⟨.or, [11, 13]⟩,
      ⟨.or, [12, 14]⟩,
      ⟨.or, [8, 19]⟩,
      ⟨.and, [0, 20]⟩,
      ⟨.or, [15, 18]⟩,
      ⟨.and, [1, 22]⟩,
      ⟨.or, [10, 16]⟩,
      ⟨.and, [2, 24]⟩,
      ⟨.or, [12, 17]⟩,
      ⟨.and, [3, 26]⟩,
      ⟨.or, [14, 18]⟩,
      ⟨.and, [4, 28]⟩,
      ⟨.or, [11, 17]⟩,
      ⟨.and, [5, 30]⟩,
      ⟨.or, [13, 16]⟩,
      ⟨.and, [6, 32]⟩,
      ⟨.or, [9, 19]⟩,
      ⟨.and, [7, 34]⟩,
      ⟨.or, [21, 23]⟩,
      ⟨.or, [36, 25]⟩,
      ⟨.or, [37, 27]⟩,
      ⟨.or, [38, 29]⟩,
      ⟨.or, [39, 31]⟩,
      ⟨.or, [40, 33]⟩,
      ⟨.or, [41, 35]⟩], 42⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
