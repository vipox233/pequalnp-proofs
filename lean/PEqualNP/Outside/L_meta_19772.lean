import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19772 :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 8 => (5496967495809117315 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  refine ⟨⟨[⟨.or, [4, 2]⟩,
      ⟨.or, [16, 0]⟩,
      ⟨.and, [17, 15]⟩,
      ⟨.or, [16, 3]⟩,
      ⟨.and, [19, 12]⟩,
      ⟨.or, [5, 2]⟩,
      ⟨.or, [21, 0]⟩,
      ⟨.and, [22, 9]⟩,
      ⟨.or, [5, 3]⟩,
      ⟨.or, [24, 1]⟩,
      ⟨.and, [25, 13]⟩,
      ⟨.or, [6, 3]⟩,
      ⟨.or, [27, 0]⟩,
      ⟨.and, [28, 8]⟩,
      ⟨.or, [7, 5]⟩,
      ⟨.or, [30, 1]⟩,
      ⟨.and, [31, 10]⟩,
      ⟨.or, [7, 6]⟩,
      ⟨.or, [33, 1]⟩,
      ⟨.and, [34, 11]⟩,
      ⟨.or, [33, 4]⟩,
      ⟨.and, [36, 14]⟩,
      ⟨.or, [18, 20]⟩,
      ⟨.or, [38, 23]⟩,
      ⟨.or, [39, 26]⟩,
      ⟨.or, [40, 29]⟩,
      ⟨.or, [41, 32]⟩,
      ⟨.or, [42, 35]⟩,
      ⟨.or, [43, 37]⟩], 44⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide +kernel
