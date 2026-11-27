import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22015 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18237 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[
    ⟨.not, [1]⟩,
    ⟨.and, [0, 6]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [8, 5]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [2, 10]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.or, [7, 11]⟩,
    ⟨.or, [13, 12]⟩
  ], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
