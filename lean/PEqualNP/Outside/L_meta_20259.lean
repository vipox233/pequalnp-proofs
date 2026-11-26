import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_20259 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15920575138259738475 : ℕ).testBit (8 * u.val + v.val)) 29 := by
  -- Six opposite-shore OR identifications, then a shared five-product decoder.
  refine ⟨⟨[⟨GateOp.or, [0, 10]⟩,
     ⟨GateOp.or, [2, 12]⟩,
     ⟨GateOp.or, [3, 11]⟩,
     ⟨GateOp.or, [4, 8]⟩,
     ⟨GateOp.or, [5, 14]⟩,
     ⟨GateOp.or, [7, 9]⟩,
     ⟨GateOp.or, [19, 20]⟩,
     ⟨GateOp.or, [16, 17]⟩,
     ⟨GateOp.or, [17, 21]⟩,
     ⟨GateOp.or, [19, 6]⟩,
     ⟨GateOp.or, [6, 13]⟩,
     ⟨GateOp.or, [1, 15]⟩,
     ⟨GateOp.or, [20, 27]⟩,
     ⟨GateOp.or, [21, 22]⟩,
     ⟨GateOp.or, [1, 29]⟩,
     ⟨GateOp.or, [13, 30]⟩,
     ⟨GateOp.or, [16, 30]⟩,
     ⟨GateOp.or, [15, 32]⟩,
     ⟨GateOp.or, [17, 27]⟩,
     ⟨GateOp.or, [13, 34]⟩,
     ⟨GateOp.and, [18, 33]⟩,
     ⟨GateOp.and, [23, 31]⟩,
     ⟨GateOp.and, [25, 35]⟩,
     ⟨GateOp.and, [24, 28]⟩,
     ⟨GateOp.and, [26, 22]⟩,
     ⟨GateOp.or, [36, 37]⟩,
     ⟨GateOp.or, [41, 38]⟩,
     ⟨GateOp.or, [42, 39]⟩,
     ⟨GateOp.or, [43, 40]⟩], 44⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
