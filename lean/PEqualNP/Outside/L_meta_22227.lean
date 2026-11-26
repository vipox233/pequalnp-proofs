import PEqualNP.Defs

set_option maxRecDepth 16000 in
set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.L_meta_22227 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (849779 : ℕ).testBit (6 * u.val + v.val)) 12 := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[⟨.or, [1, 5]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [2, 14]⟩, ⟨.and, [10, 15]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [6, 17]⟩, ⟨.or, [0, 18]⟩, ⟨.and, [13, 19]⟩, ⟨.or, [4, 20]⟩], 21⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, C]
  · decide +kernel
