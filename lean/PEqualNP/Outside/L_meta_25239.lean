import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25239 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50335 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.not, [7]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.not, [14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
