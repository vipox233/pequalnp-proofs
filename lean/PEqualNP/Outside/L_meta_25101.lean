import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25101 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274861887 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [7]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [8, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
