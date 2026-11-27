import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21523 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266719 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [0]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.not, [8]⟩
  ], 9⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
