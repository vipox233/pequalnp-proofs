import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25237 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50107 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.and, [6, 7]⟩, ⟨.not, [2]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 8]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
