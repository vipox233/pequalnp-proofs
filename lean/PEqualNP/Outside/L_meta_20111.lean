import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20111 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17056109459091738360 : ℕ).testBit (8 * u.val + v.val)) 33) := by
  refine ⟨⟨[
    ⟨.or, [8, 9]⟩,
    ⟨.or, [11, 13]⟩,
    ⟨.or, [10, 16]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [12, 15]⟩,
    ⟨.or, [10, 20]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [18, 19]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.or, [17, 22]⟩,
    ⟨.or, [22, 24]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [15, 23]⟩,
    ⟨.or, [16, 26]⟩,
    ⟨.or, [8, 23]⟩,
    ⟨.or, [18, 21]⟩,
    ⟨.and, [4, 29]⟩,
    ⟨.and, [2, 25]⟩,
    ⟨.and, [5, 32]⟩,
    ⟨.and, [3, 33]⟩,
    ⟨.and, [6, 31]⟩,
    ⟨.and, [1, 28]⟩,
    ⟨.and, [7, 27]⟩,
    ⟨.and, [0, 30]⟩,
    ⟨.or, [34, 35]⟩,
    ⟨.or, [36, 42]⟩,
    ⟨.or, [37, 43]⟩,
    ⟨.or, [38, 44]⟩,
    ⟨.or, [39, 45]⟩,
    ⟨.or, [40, 46]⟩,
    ⟨.or, [41, 47]⟩], 48⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel
