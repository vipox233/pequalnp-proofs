import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24821 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2148157 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
