import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22233 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17966 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 3]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [7, 5]⟩, ⟨.not, [8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [0, 12]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [16, 15]⟩], 17⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
