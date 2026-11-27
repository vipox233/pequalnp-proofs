import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25179 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17339 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.not, [11]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
