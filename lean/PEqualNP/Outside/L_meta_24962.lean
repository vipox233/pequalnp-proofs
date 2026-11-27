import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24962 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6374831 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.not, [4]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [10, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
