import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20281 :
    PEqualNP.Represents.RepSizeAtMost
      (fun u v : Fin 8 => (1432153032174414900 : ℕ).testBit (8 * u.val + v.val)) 24 := by
  refine ⟨⟨[
      ⟨.or, [1, 9]⟩,
      ⟨.or, [5, 11]⟩,
      ⟨.or, [7, 17]⟩,
      ⟨.and, [16, 18]⟩,
      ⟨.or, [0, 14]⟩,
      ⟨.or, [16, 20]⟩,
      ⟨.or, [17, 21]⟩,
      ⟨.or, [3, 10]⟩,
      ⟨.and, [22, 23]⟩,
      ⟨.or, [19, 24]⟩,
      ⟨.or, [4, 8]⟩,
      ⟨.or, [2, 12]⟩,
      ⟨.or, [7, 15]⟩,
      ⟨.or, [18, 28]⟩,
      ⟨.or, [27, 29]⟩,
      ⟨.and, [26, 30]⟩,
      ⟨.or, [25, 31]⟩,
      ⟨.or, [6, 21]⟩,
      ⟨.and, [13, 33]⟩,
      ⟨.or, [6, 27]⟩,
      ⟨.or, [20, 28]⟩,
      ⟨.and, [35, 36]⟩,
      ⟨.or, [34, 37]⟩,
      ⟨.or, [32, 38]⟩], 39⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
