import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24201 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (14897087 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.and, [2, 3]⟩, ⟨.not, [7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [1, 10]⟩], 11⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
