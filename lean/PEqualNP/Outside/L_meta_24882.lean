import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24882 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2213815 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
