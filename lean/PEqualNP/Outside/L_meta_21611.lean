import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21611 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4168 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.and,[0,3]⟩,⟨.and,[1,2]⟩,⟨.or,[4,6]⟩,⟨.or,[3,7]⟩,⟨.or,[0,8]⟩,⟨.not,[9]⟩,⟨.or,[5,10]⟩],11⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
