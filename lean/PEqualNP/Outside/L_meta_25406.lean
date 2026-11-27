import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25406 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (6474815 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [3, 4]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [1, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [8, 11]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
