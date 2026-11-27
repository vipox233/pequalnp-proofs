import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24830 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149813 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [5, 7]⟩, ⟨.not, [7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.not, [13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
