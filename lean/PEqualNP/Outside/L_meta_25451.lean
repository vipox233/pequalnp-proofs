import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25451 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 16 C ∧ C.size ≤ 30 ∧ PEqualNP.Represents.Represents (fun u v : Fin 8 => (14365273235675442750 : ℕ).testBit (8 * u.val + v.val)) C := by
  refine ⟨⟨[⟨.or, [6, 13]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [20, 9]⟩, ⟨.or, [21, 18]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [23, 19]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [25, 7]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [27, 15]⟩, ⟨.or, [0, 19]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [30, 17]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [34, 18]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [22, 24]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [29, 31]⟩, ⟨.and, [32, 33]⟩, ⟨.and, [35, 36]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [43, 40]⟩, ⟨.or, [44, 41]⟩], 45⟩, ?_, by decide, by decide +kernel⟩
  simp [PEqualNP.MetaComplexity.Monotone2]
