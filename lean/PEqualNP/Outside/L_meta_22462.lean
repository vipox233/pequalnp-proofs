import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22462 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17084 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 2]⟩,
    ⟨.or, [6, 4]⟩,
    ⟨.or, [7, 5]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [11, 4]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [16, 5]⟩,
    ⟨.and, [0, 17]⟩,
    ⟨.or, [10, 15]⟩,
    ⟨.or, [19, 18]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
