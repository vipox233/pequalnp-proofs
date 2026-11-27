import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22598 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17035 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [3, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 9]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [11, 8]⟩,
    ⟨.or, [12, 10]⟩,
    ⟨.not, [13]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
