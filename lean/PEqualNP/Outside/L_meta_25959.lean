import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25959 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 7, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨⟨[⟨.or, [0, 1]⟩, ⟨.not, [7]⟩, ⟨.and, [8, 9]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [10, 11]⟩], 12⟩,
    by simp [PEqualNP.MetaComplexity.FanInTwo],
    by decide,
    by decide,
    by decide +kernel⟩
