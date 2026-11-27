import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24724 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (52667 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.not, [3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
