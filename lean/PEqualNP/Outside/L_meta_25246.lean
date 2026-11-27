import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25246 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (50716 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  refine ⟨(⟨[⟨.or, [3, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [5, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [6, 7]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [11, 12]⟩], 13⟩ : PEqualNP.CircuitLowerBounds.Circuit), ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
