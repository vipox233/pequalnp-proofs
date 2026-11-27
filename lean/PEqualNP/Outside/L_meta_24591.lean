import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24591 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270549951 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [4, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.not, [11]⟩, ⟨.or, [0, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
