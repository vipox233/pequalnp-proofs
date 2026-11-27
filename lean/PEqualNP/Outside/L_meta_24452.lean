import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24452 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (101035 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [2, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [4, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [8, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
