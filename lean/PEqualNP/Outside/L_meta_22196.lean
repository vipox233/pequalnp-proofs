import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22196 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17177 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 2]⟩,
      ⟨.or, [6, 5]⟩,
      ⟨.not, [7]⟩,
      ⟨.and, [0, 8]⟩,
      ⟨.or, [0, 3]⟩,
      ⟨.or, [10, 4]⟩,
      ⟨.or, [11, 5]⟩,
      ⟨.not, [12]⟩,
      ⟨.and, [2, 13]⟩,
      ⟨.and, [1, 3]⟩,
      ⟨.or, [9, 14]⟩,
      ⟨.or, [16, 15]⟩], 17⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
