import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25245 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50622 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.not, [6]⟩, ⟨.or, [5, 3]⟩, ⟨.not, [8]⟩, ⟨.or, [8, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.and, [10, 0]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [11, 14]⟩], 15⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
