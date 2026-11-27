import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22581 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (389 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩,
      ⟨.not, [6]⟩,
      ⟨.and, [2, 7]⟩,
      ⟨.and, [0, 1]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.or, [10, 5]⟩,
      ⟨.or, [11, 8]⟩,
      ⟨.or, [12, 9]⟩,
      ⟨.not, [13]⟩], 14⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
