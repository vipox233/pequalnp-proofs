import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25165 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17053 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
