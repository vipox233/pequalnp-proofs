import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25193 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18234 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [12, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
