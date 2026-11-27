import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22350 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17050 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [2, 4]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [10, 3]⟩,
    ⟨.or, [11, 4]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [0, 16]⟩,
    ⟨.or, [9, 15]⟩,
    ⟨.or, [18, 17]⟩
  ], 19⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
