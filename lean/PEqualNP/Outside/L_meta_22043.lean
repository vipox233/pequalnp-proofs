import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22043 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816892 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := [
        ⟨.or, [3, 8]⟩,
        ⟨.or, [4, 5]⟩,
        ⟨.or, [9, 10]⟩,
        ⟨.or, [2, 8]⟩,
        ⟨.or, [0, 11]⟩,
        ⟨.or, [1, 6]⟩,
        ⟨.or, [14, 15]⟩,
        ⟨.or, [12, 15]⟩,
        ⟨.and, [14, 17]⟩,
        ⟨.or, [7, 18]⟩,
        ⟨.or, [13, 19]⟩,
        ⟨.and, [16, 20]⟩]
      output := 21 }
  refine ⟨circuit, ?_, by decide, ?_⟩
  · intro g hg
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
