import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23595 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (33975 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [2, 3]⟩, ⟨.not, [3]⟩, ⟨.or, [2, 5]⟩,
      ⟨.not, [8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩,
      ⟨.and, [7, 11]⟩, ⟨.or, [6, 12]⟩], 13⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
