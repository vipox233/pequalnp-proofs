import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24805 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147358 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [7, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
