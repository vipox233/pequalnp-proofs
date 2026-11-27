import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25315 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2165423 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
