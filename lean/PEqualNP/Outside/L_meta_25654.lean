import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25654 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
  PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
  PEqualNP.Represents.Represents (fun (u v : Fin 5) => decide (v.val = u.val ∨ v.val = (u.val + 1) % 5)) C := by
  refine ⟨⟨[⟨.or, [2, 5]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [4, 7]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [15, 12]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [10, 15]⟩, ⟨.and, [17, 18]⟩, ⟨.and, [11, 16]⟩, ⟨.or, [19, 20]⟩], 21⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.FanInTwo]
