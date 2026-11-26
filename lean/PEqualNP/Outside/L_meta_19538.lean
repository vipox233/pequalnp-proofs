import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_19538 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.Represents.Represents (fun u v : Fin 4 => (279 : ℕ).testBit (4 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [0, 4]⟩, ⟨.or, [3, 7]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩], 11⟩, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.FanInTwo]
  · decide
  · decide +kernel
