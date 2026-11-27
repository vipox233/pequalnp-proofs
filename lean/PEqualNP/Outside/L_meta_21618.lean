import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21618 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4368 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[
    ⟨.and, [0, 4]⟩,
    ⟨.and, [1, 3]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [7, 3]⟩,
    ⟨.or, [8, 4]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.or, [5, 6]⟩,
    ⟨.or, [12, 11]⟩
  ], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
