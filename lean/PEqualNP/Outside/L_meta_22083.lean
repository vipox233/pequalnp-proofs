import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22083 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16919 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.or, [3, 5]⟩,
    ⟨.not, [6]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.or, [10, 5]⟩,
    ⟨.not, [11]⟩,
    ⟨.and, [2, 12]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [8, 13]⟩,
    ⟨.or, [15, 14]⟩
  ], 16⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
