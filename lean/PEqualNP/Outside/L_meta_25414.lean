import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25414 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6491835 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.not, [2]⟩, ⟨.or, [4, 5]⟩, ⟨.not, [5]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [8, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.and, [9, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
