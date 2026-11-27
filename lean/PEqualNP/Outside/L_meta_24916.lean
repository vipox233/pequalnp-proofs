import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24916 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4295087 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.not, [7]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
