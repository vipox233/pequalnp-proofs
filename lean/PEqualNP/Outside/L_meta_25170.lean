import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25170 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17179 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [0]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [1, 13]⟩, ⟨.and, [9, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
