import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25195 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18363 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.not, [10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [5, 12]⟩, ⟨.and, [8, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
