import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21758 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (807641 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or,[2,3]⟩,⟨.or,[1,5]⟩,⟨.or,[0,6]⟩,⟨.or,[0,3]⟩,⟨.or,[1,2]⟩,⟨.and,[8,9]⟩,⟨.not,[10]⟩,⟨.and,[7,11]⟩],12⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
