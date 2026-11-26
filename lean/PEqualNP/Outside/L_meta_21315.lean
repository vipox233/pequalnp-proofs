import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_21315 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103804 : ℕ).testBit (5 * u.val + v.val)) 11) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [7, 2]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [1, 16]⟩, ⟨.and, [14, 17]⟩, ⟨.or, [13, 18]⟩], 19⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp [C] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp
