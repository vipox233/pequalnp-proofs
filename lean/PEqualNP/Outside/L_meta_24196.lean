import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24196 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6408095 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [8, 10]⟩], 11⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
