import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25291 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2149438 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.and, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [2, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [11, 12]⟩, ⟨.or, [10, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
