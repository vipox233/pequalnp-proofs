import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22346 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 14 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (16569 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.not,[0]⟩,⟨.and,[3,6]⟩,⟨.not,[0]⟩,⟨.and,[4,8]⟩,⟨.not,[0]⟩,⟨.and,[5,10]⟩,⟨.or,[0,2]⟩,⟨.and,[1,12]⟩,⟨.and,[2,0]⟩,⟨.or,[7,9]⟩,⟨.or,[15,11]⟩,⟨.or,[16,13]⟩,⟨.or,[17,14]⟩,⟨.not,[18]⟩],19⟩, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
