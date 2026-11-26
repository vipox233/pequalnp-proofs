import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_20392 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6839164070987673195 : ℕ).testBit (8 * u.val + v.val)) 30 := by
  -- Five compatible zero merges; then an exact five-product quotient decoder.
  -- Quotient cut-cover method adapted from the L-meta-20259 worker.
  refine ⟨⟨[⟨GateOp.or, [0, 10]⟩,
     ⟨GateOp.or, [2, 11]⟩,
     ⟨GateOp.or, [4, 8]⟩,
     ⟨GateOp.or, [5, 13]⟩,
     ⟨GateOp.or, [6, 12]⟩,
     ⟨GateOp.or, [17, 9]⟩,
     ⟨GateOp.or, [1, 14]⟩,
     ⟨GateOp.or, [21, 22]⟩,
     ⟨GateOp.or, [16, 7]⟩,
     ⟨GateOp.or, [19, 3]⟩,
     ⟨GateOp.or, [15, 25]⟩,
     ⟨GateOp.or, [17, 25]⟩,
     ⟨GateOp.or, [14, 27]⟩,
     ⟨GateOp.or, [16, 20]⟩,
     ⟨GateOp.or, [3, 29]⟩,
     ⟨GateOp.or, [18, 19]⟩,
     ⟨GateOp.or, [7, 31]⟩,
     ⟨GateOp.or, [18, 20]⟩,
     ⟨GateOp.or, [15, 33]⟩,
     ⟨GateOp.or, [20, 1]⟩,
     ⟨GateOp.or, [9, 35]⟩,
     ⟨GateOp.and, [28, 34]⟩,
     ⟨GateOp.and, [23, 24]⟩,
     ⟨GateOp.and, [30, 32]⟩,
     ⟨GateOp.and, [36, 26]⟩,
     ⟨GateOp.and, [21, 22]⟩,
     ⟨GateOp.or, [37, 38]⟩,
     ⟨GateOp.or, [42, 39]⟩,
     ⟨GateOp.or, [43, 40]⟩,
     ⟨GateOp.or, [44, 41]⟩], 45⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
