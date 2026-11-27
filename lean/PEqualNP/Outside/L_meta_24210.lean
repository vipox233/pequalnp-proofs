import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24210 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (270585791 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [4, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
