import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24438 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (100027 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [1, 8]⟩, ⟨.not, [8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 12]⟩], 13⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
