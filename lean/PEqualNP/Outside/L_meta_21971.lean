import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21971 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (156 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [0, 2]⟩,
    ⟨.or, [6, 3]⟩,
    ⟨.or, [7, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [12, 4]⟩,
    ⟨.and, [0, 13]⟩,
    ⟨.or, [11, 14]⟩
  ], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
