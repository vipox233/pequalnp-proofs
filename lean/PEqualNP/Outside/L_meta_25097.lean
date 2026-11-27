import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25097 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (274844077 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [0, 1]⟩, ⟨.not, [5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.and, [6, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [8, 13]⟩], 14⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
