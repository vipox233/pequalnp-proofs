import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25162 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16955 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [1, 5]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [1, 7]⟩, ⟨.not, [2]⟩, ⟨.not, [9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [10, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
