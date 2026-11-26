import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19868 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1970952436485043335 : ℕ).testBit (8 * u.val + v.val)) 31) := by
  refine ⟨⟨[
    ⟨.or, [9, 11]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [12, 16]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [14, 19]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [21, 17]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [24, 17]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [15, 20]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [10, 20]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.or, [31, 17]⟩,
    ⟨.and, [4, 32]⟩,
    ⟨.or, [13, 18]⟩,
    ⟨.and, [5, 34]⟩,
    ⟨.or, [14, 18]⟩,
    ⟨.and, [6, 36]⟩,
    ⟨.or, [8, 18]⟩,
    ⟨.and, [7, 38]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [40, 28]⟩,
    ⟨.or, [41, 30]⟩,
    ⟨.or, [42, 33]⟩,
    ⟨.or, [43, 35]⟩,
    ⟨.or, [44, 37]⟩,
    ⟨.or, [45, 39]⟩], 46⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
