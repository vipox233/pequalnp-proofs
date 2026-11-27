import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24861 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2183103 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [9, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
