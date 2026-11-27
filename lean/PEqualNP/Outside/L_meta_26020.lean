import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26020 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 5 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([15, 15, 13, 3] : List ℕ).getD u.val 0).testBit v.val) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.and, [2, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.not, [11]⟩], 12⟩
  refine ⟨C, ?_, by decide, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp
