import PEqualNP.Defs

set_option maxRecDepth 4096 in
theorem PEqualNP.Outside.L_meta_20266 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10184235645427475370 : ℕ).testBit (8 * u.val + v.val)) 28 := by
  refine ⟨⟨[
    ⟨.or, [11, 2]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.or, [13, 6]⟩,
    ⟨.or, [15, 4]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.or, [18, 1]⟩,
    ⟨.or, [16, 15]⟩,
    ⟨.and, [19, 16]⟩,
    ⟨.or, [17, 22]⟩,
    ⟨.or, [1, 17]⟩,
    ⟨.or, [22, 25]⟩,
    ⟨.or, [20, 25]⟩,
    ⟨.or, [27, 14]⟩,
    ⟨.or, [22, 21]⟩,
    ⟨.or, [8, 0]⟩,
    ⟨.or, [26, 30]⟩,
    ⟨.and, [24, 20]⟩,
    ⟨.or, [4, 18]⟩,
    ⟨.and, [30, 29]⟩,
    ⟨.and, [25, 14]⟩,
    ⟨.or, [7, 23]⟩,
    ⟨.or, [9, 36]⟩,
    ⟨.and, [28, 33]⟩,
    ⟨.and, [31, 37]⟩,
    ⟨.or, [39, 35]⟩,
    ⟨.or, [32, 38]⟩,
    ⟨.or, [40, 34]⟩,
    ⟨.or, [42, 41]⟩], 43⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
