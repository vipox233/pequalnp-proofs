import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24461 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101309 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [10, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
