import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23267 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4310975 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [3, 4]⟩,
    ⟨.not, [5]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [1, 8]⟩,
    ⟨.and, [7, 9]⟩,
    ⟨.or, [0, 10]⟩
  ], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
