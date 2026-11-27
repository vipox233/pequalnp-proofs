import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24949 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4362047 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [7, 11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
