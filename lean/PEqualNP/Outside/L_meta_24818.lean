import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24818 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148127 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.not, [4]⟩, ⟨.or, [1, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.and, [9, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
