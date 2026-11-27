import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24181 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266906 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨⟨[⟨.or, [4, 0]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [1, 8]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.not, [12]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [7, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
