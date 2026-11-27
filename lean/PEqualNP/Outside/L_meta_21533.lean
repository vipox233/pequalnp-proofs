import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21533 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (199 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.not, [5]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [8, 4]⟩, ⟨.not, [9]⟩], 10⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
