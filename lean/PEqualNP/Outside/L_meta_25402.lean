import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25402 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6409655 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.and, [5, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.not, [12]⟩, ⟨.or, [10, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
