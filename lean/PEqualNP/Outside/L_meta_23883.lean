import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23883 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12619 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.not, [8]⟩, ⟨.and, [9, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
