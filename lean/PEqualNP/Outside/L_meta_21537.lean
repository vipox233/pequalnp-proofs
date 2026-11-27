import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21537 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (219 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not, [2]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [7]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [6, 9]⟩], 10⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
