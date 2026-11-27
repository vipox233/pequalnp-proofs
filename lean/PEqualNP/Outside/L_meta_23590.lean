import PEqualNP.Defs

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_23590 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33951 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.not, [5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.not, [8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [6, 12]⟩], 13⟩

  exact ⟨circuit, by simp [PEqualNP.MetaComplexity.FanInTwo, circuit],
    by decide +kernel, by decide +kernel⟩
