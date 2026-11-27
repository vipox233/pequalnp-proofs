import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23039 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (102204 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [0, 1]⟩,
      ⟨.or, [2, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [4, 10]⟩,
      ⟨.or, [3, 11]⟩, ⟨.and, [7, 12]⟩], 13⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.Monotone2]
