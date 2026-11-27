import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22088 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16955 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.not, [2]⟩,
      ⟨.and, [0, 6]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.or, [8, 3]⟩,
      ⟨.or, [9, 4]⟩,
      ⟨.or, [10, 5]⟩,
      ⟨.not, [11]⟩,
      ⟨.and, [2, 12]⟩,
      ⟨.and, [1, 3]⟩,
      ⟨.or, [7, 13]⟩,
      ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
