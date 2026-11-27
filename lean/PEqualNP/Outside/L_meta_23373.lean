import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23373 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (99995 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [2, 5]⟩,
      ⟨.not, [8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [3, 10]⟩,
      ⟨.and, [7, 11]⟩], 12⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
