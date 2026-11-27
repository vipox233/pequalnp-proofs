import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_22005 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17206 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  refine ⟨⟨[⟨.or,[3,4]⟩,⟨.or,[6,5]⟩,⟨.not,[7]⟩,⟨.and,[2,8]⟩,⟨.or,[1,4]⟩,⟨.or,[10,5]⟩,⟨.and,[0,11]⟩,⟨.and,[1,3]⟩,⟨.or,[9,12]⟩,⟨.or,[14,13]⟩],15⟩,?_,by decide,by decide +kernel⟩
  intro g hg
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
