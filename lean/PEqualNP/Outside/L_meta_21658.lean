import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21658 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13150 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.not, [2]⟩,
    ⟨.and, [1, 5]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.and, [0, 10]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.or, [12, 11]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
