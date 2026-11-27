import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22534 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18239 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [3, 4]⟩,
      ⟨.and, [1, 6]⟩,
      ⟨.or, [5, 6]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [2, 9]⟩,
      ⟨.or, [0, 10]⟩,
      ⟨.or, [7, 11]⟩], 12⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
