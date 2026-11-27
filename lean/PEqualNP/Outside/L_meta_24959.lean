import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24959 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4427583 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [0, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
