import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22021 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33683 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or,[4,5]⟩,⟨.not,[6]⟩,⟨.and,[1,7]⟩,⟨.or,[2,3]⟩,⟨.or,[9,5]⟩,⟨.not,[10]⟩,⟨.and,[0,11]⟩,⟨.and,[2,3]⟩,⟨.or,[8,12]⟩,⟨.or,[14,13]⟩],15⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
