import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24262 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16543 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [7, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [9, 11]⟩], 12⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
