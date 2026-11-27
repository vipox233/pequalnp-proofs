import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24498 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147262 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.not, [6]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [7, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
