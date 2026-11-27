import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24495 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2147230 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
