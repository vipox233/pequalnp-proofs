import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22242 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18238 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩,
      ⟨.and, [1, 6]⟩,
      ⟨.or, [5, 6]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [2, 9]⟩,
      ⟨.or, [1, 3]⟩,
      ⟨.or, [4, 11]⟩,
      ⟨.or, [5, 12]⟩,
      ⟨.and, [0, 13]⟩,
      ⟨.or, [10, 14]⟩,
      ⟨.or, [7, 15]⟩], 16⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
