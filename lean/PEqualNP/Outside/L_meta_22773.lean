import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22773 :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (1948535 : ℕ).testBit (6 * u.val + v.val)) 14 := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [0, 1]⟩,
      ⟨.or, [6, 9]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [0, 2]⟩,
      ⟨.or, [5, 8]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [5, 6]⟩,
      ⟨.and, [3, 18]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [14, 20]⟩,
      ⟨.or, [17, 21]⟩, ⟨.or, [19, 22]⟩], 23⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
