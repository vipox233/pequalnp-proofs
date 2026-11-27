import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22095 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17178 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 3]⟩,
    ⟨.or, [6, 4]⟩,
    ⟨.or, [7, 5]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [2, 9]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [11, 4]⟩,
    ⟨.and, [0, 12]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [10, 13]⟩,
    ⟨.or, [15, 14]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
