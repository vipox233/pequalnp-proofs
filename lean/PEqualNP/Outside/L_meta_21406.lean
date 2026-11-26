import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21406 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241149 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [6, 7]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [0, 10]⟩,
      ⟨.or, [1, 2]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [12, 13]⟩,
      ⟨.or, [1, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [15, 16]⟩,
      ⟨.or, [11, 14]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [19, 4]⟩], 20⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
