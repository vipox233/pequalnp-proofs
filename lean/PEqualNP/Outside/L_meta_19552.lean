import PEqualNP.Defs

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_19552 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (0xc3b478740f9a8b65 : ℕ).testBit (8 * u.val + v.val)) 28) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [6, 8]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [2, 14]⟩,
      ⟨.or, [7, 12]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [16, 18]⟩,
      ⟨.or, [0, 15]⟩, ⟨.or, [22, 19]⟩, ⟨.or, [0, 11]⟩,
      ⟨.or, [24, 16]⟩, ⟨.or, [25, 20]⟩, ⟨.or, [3, 10]⟩,
      ⟨.or, [27, 17]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [29, 19]⟩,
      ⟨.or, [5, 15]⟩, ⟨.or, [31, 20]⟩, ⟨.or, [2, 5]⟩,
      ⟨.or, [33, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [21, 23]⟩,
      ⟨.and, [26, 28]⟩, ⟨.and, [30, 32]⟩, ⟨.and, [34, 35]⟩,
      ⟨.or, [36, 37]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [41, 39]⟩], 42⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp [C] at hg
    rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst g <;> simp
  · decide +kernel
