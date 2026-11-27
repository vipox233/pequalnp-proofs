import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24499 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147359 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 4]⟩, ⟨.not, [5]⟩, ⟨.not, [6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.and, [7, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
