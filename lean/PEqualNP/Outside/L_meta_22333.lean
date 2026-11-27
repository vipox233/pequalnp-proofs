import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22333 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18109 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [1]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [8, 5]⟩, ⟨.not, [9]⟩, ⟨.and, [1, 10]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [13, 5]⟩, ⟨.not, [14]⟩, ⟨.and, [2, 15]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [17, 16]⟩], 18⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
