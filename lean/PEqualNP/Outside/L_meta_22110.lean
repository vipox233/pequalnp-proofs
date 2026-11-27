import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22110 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17967 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [4]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.or, [9, 5]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [2, 11]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [1, 13]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [15, 14]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
