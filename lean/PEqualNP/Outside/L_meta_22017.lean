import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22017 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20031 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, 3]⟩,
      ⟨.or, [6, 4]⟩,
      ⟨.or, [7, 5]⟩,
      ⟨.not, [8]⟩,
      ⟨.and, [2, 9]⟩,
      ⟨.or, [3, 4]⟩,
      ⟨.or, [11, 5]⟩,
      ⟨.and, [1, 12]⟩,
      ⟨.or, [0, 10]⟩,
      ⟨.or, [14, 13]⟩], 15⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
