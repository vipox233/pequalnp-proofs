import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24140 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (279454 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [2, 4]⟩, ⟨.and, [2, 4]⟩, ⟨.not, [5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [5, 11]⟩, ⟨.or, [12, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
