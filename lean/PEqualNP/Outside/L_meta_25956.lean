import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25956 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([7, 2, 1, 0] : List ℕ).getD u.val 0).testBit v.val) C :=
  ⟨⟨[⟨.not, [7]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [1, 5]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [12, 11]⟩], 13⟩,
    by simp [PEqualNP.MetaComplexity.FanInTwo], by decide, by decide, by decide +kernel⟩
