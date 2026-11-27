import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22321 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18092 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [0, 2]⟩, ⟨.or, [6, 5]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [10, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.not, [12]⟩, ⟨.and, [2, 13]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [0, 15]⟩, ⟨.or, [9, 14]⟩, ⟨.or, [17, 16]⟩], 18⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
