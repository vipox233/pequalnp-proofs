import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23931 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 5,
        C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (4368 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [3, 4]⟩,
      ⟨.or, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [9]⟩,
      ⟨.or, [6, 10]⟩, ⟨.or, [5, 11]⟩], 12⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
