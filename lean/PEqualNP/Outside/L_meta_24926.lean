import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_24926 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4310952 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or, [1, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [11, 13]⟩], 14⟩, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide +kernel
