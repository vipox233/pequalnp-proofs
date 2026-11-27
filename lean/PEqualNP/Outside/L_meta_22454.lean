import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22454 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (20024 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [7, 5]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [6, 8]⟩,
    ⟨.or, [10, 11]⟩
  ], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
