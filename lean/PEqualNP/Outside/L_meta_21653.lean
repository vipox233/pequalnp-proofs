import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21653 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 5,
        C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
          (12763 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [0, 2]⟩, ⟨.not, [5]⟩, ⟨.or, [1, 2]⟩,
      ⟨.not, [4]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [6, 10]⟩], 11⟩
  refine ⟨circuit, ?_, by decide +kernel, by decide +kernel⟩
  simp [circuit, PEqualNP.MetaComplexity.FanInTwo]
