import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25263 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50994 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [0, 10]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [8, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
