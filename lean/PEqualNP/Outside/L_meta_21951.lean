import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21951 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33684 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 4]⟩,
    ⟨.or, [6, 5]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.and, [0, 4]⟩,
    ⟨.or, [9, 11]⟩,
    ⟨.or, [13, 12]⟩
  ], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
