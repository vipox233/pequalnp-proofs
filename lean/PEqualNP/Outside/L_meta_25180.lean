import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25180 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17340 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.not, [8]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
