import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21918 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (830 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or,[0,1]⟩,⟨.or,[4,5]⟩,⟨.or,[1,7]⟩,⟨.and,[0,8]⟩,⟨.or,[3,9]⟩,⟨.or,[2,10]⟩,⟨.and,[6,11]⟩],12⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
