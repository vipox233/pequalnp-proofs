import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23932 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4373 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [0, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [5, 11]⟩], 12⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
