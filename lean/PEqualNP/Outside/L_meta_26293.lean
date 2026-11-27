import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_26293 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin 4) (v : Fin 4) => (([14, 1, 1, 1] : List ℕ).getD u.val 0).testBit v.val) C) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 4]⟩, ⟨.and, [0, 4]⟩, ⟨.not, [9]⟩, ⟨.and, [8, 10]⟩], 11⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp
