import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24922 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4296637 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [3, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [0, 8]⟩, ⟨.not, [11]⟩, ⟨.and, [10, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
