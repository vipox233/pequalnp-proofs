import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22791 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4028141 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [5, 8]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [11, 9]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.or, [10, 7]⟩,
    ⟨.and, [1, 14]⟩,
    ⟨.or, [10, 6]⟩,
    ⟨.and, [2, 16]⟩,
    ⟨.or, [11, 5]⟩,
    ⟨.and, [3, 18]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.or, [17, 19]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [22, 4]⟩
  ], 23⟩
  refine ⟨circuit, ?_, by decide, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
