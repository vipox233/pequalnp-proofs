import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21638 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8653 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 4]⟩,
      ⟨.not, [5]⟩,
      ⟨.and, [0, 6]⟩,
      ⟨.or, [0, 4]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [1, 9]⟩,
      ⟨.and, [2, 3]⟩,
      ⟨.or, [7, 10]⟩,
      ⟨.or, [12, 11]⟩], 13⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
