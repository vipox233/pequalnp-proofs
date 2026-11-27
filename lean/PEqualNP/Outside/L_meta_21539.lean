import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21539 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (398 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 3]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [7, 9]⟩
  ], 10⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
