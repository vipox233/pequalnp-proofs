import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24161 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266907 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [4, 8]⟩, ⟨.and, [6, 9]⟩, ⟨.or, [6, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
