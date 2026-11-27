import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_23245 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (116655 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.not, [5]⟩, ⟨.not, [4]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
