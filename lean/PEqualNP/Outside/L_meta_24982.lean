import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24982 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6507967 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [3, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
