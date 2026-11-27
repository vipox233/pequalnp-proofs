import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22776 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (1948665 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [10, 11]⟩,
      ⟨.or, [0, 2]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [13, 14]⟩,
      ⟨.or, [0, 1]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [16, 17]⟩,
      ⟨.and, [2, 5]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [15, 20]⟩,
      ⟨.or, [18, 21]⟩, ⟨.or, [19, 22]⟩], 23⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
