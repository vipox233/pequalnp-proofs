import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21973 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (190 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
