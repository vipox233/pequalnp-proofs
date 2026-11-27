import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22278 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16915 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  let witness : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [2, 3]⟩,
      ⟨.or, [6, 5]⟩,
      ⟨.not, [7]⟩,
      ⟨.and, [0, 8]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.or, [10, 3]⟩,
      ⟨.or, [11, 4]⟩,
      ⟨.or, [12, 5]⟩,
      ⟨.not, [13]⟩,
      ⟨.and, [2, 14]⟩,
      ⟨.and, [1, 3]⟩,
      ⟨.or, [9, 15]⟩,
      ⟨.or, [17, 16]⟩], 18⟩
  refine ⟨witness, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo, witness]
  · decide +kernel
