import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21746 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (275030 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 4]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [4, 12]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [14, 13]⟩,
    ⟨.not, [15]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
