import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22555 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (33714 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 7]⟩,
      ⟨.not, [7]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [8, 10]⟩,
      ⟨.or, [6, 11]⟩], 12⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
