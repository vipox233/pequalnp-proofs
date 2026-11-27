import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22139 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33948 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 2]⟩,
      ⟨.or, [6, 3]⟩,
      ⟨.or, [7, 5]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [1, 9]⟩,
      ⟨.or, [2, 3]⟩,
      ⟨.or, [11, 4]⟩,
      ⟨.and, [0, 12]⟩,
      ⟨.and, [2, 3]⟩,
      ⟨.or, [10, 13]⟩,
      ⟨.or, [15, 14]⟩], 16⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
