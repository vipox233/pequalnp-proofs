import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_19792 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6572913902839198155 : ℕ).testBit (8 * u.val + v.val)) 34 := by
  refine ⟨⟨[⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [8, 15]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [22, 19]⟩, ⟨GateOp.and, [0, 23]⟩, ⟨GateOp.or, [13, 18]⟩, ⟨GateOp.or, [25, 19]⟩, ⟨GateOp.and, [1, 26]⟩, ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.and, [2, 28]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.or, [30, 19]⟩, ⟨GateOp.and, [3, 31]⟩, ⟨GateOp.or, [10, 21]⟩, ⟨GateOp.and, [4, 33]⟩, ⟨GateOp.or, [16, 20]⟩, ⟨GateOp.and, [5, 35]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [37, 12]⟩, ⟨GateOp.or, [38, 17]⟩, ⟨GateOp.and, [6, 39]⟩, ⟨GateOp.or, [8, 21]⟩, ⟨GateOp.and, [7, 41]⟩, ⟨GateOp.or, [24, 27]⟩, ⟨GateOp.or, [43, 29]⟩, ⟨GateOp.or, [44, 32]⟩, ⟨GateOp.or, [45, 34]⟩, ⟨GateOp.or, [46, 36]⟩, ⟨GateOp.or, [47, 40]⟩, ⟨GateOp.or, [48, 42]⟩], 49⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel
