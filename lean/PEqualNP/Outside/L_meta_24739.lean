import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24739 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100029 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.not, [10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [12, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
