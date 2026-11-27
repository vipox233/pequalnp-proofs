import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26023 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 4 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 15, 11, 7] : List ℕ).getD u.val 0).testBit v.val) C) := by
  refine ⟨⟨[⟨.and, [2, 6]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩], 11⟩, ?_, by decide, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp
