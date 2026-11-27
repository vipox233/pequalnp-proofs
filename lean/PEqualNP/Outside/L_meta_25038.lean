import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25038 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270582688 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [7, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [8, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
