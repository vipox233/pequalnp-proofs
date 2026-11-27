import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21545 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (925 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [1]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [7, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
