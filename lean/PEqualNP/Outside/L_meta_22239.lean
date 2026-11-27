import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22239 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18095 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [4]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [2, 5]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [1, 9]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [11, 4]⟩,
    ⟨.or, [12, 5]⟩,
    ⟨.not, [13]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [16, 15]⟩
  ], 17⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
