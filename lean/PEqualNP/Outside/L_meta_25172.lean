import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25172 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17208 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [0, 9]⟩, ⟨.not, [11]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [6, 13]⟩, ⟨.or, [7, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
