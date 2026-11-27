import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25207 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33949 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [5, 10]⟩, ⟨.not, [12]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
