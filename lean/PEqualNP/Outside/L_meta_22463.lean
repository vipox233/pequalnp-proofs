import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22463 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 15 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18089 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [1]⟩,
    ⟨.and, [4, 6]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.not, [10]⟩,
    ⟨.and, [3, 11]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 13]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.or, [7, 9]⟩,
    ⟨.or, [16, 12]⟩,
    ⟨.or, [17, 14]⟩,
    ⟨.or, [18, 15]⟩,
    ⟨.not, [19]⟩
  ], 20⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
