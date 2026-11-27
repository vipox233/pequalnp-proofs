import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24145 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (283549 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.not, [3]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [5, 10]⟩, ⟨.not, [9]⟩, ⟨.or, [11, 12]⟩], 13⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
