import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_22946 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4029180 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  refine ⟨{
    gates := [
      ⟨.or, [0, 2]⟩,
      ⟨.or, [6, 8]⟩,
      ⟨.and, [10, 11]⟩,
      ⟨.or, [0, 1]⟩,
      ⟨.or, [7, 9]⟩,
      ⟨.and, [13, 14]⟩,
      ⟨.or, [1, 2]⟩,
      ⟨.or, [16, 3]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.and, [17, 18]⟩,
      ⟨.or, [6, 7]⟩,
      ⟨.and, [3, 20]⟩,
      ⟨.or, [12, 15]⟩,
      ⟨.or, [19, 21]⟩,
      ⟨.or, [22, 23]⟩]
    output := 24 }, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · decide
  · decide
