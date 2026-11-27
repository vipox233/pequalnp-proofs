import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24902 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2330431 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [8]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [3, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
