import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22221 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17960 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩,
      ⟨.or, [3, 6]⟩,
      ⟨.or, [4, 7]⟩,
      ⟨.or, [5, 8]⟩,
      ⟨.not, [9]⟩,
      ⟨.or, [3, 5]⟩,
      ⟨.and, [0, 11]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.and, [1, 13]⟩,
      ⟨.or, [12, 14]⟩,
      ⟨.or, [10, 15]⟩], 16⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
