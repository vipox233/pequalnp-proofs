import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25264 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50995 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [7, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [9, 13]⟩, ⟨.and, [11, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
