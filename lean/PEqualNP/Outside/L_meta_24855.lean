import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24855 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2181055 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 3]⟩, ⟨.not, [4]⟩, ⟨.or, [5, 6]⟩, ⟨.not, [8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
