import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_20051 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15612158718957067875 : ℕ).testBit (8 * u.val + v.val)) 31 := by
  let C : Circuit := ⟨[
    ⟨.or, [8, 13]⟩,
    ⟨.or, [12, 14]⟩,
    ⟨.or, [11, 15]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [9, 16]⟩,
    ⟨.or, [10, 17]⟩,
    ⟨.or, [14, 20]⟩,
    ⟨.and, [0, 22]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [24, 19]⟩,
    ⟨.and, [1, 25]⟩,
    ⟨.or, [13, 21]⟩,
    ⟨.and, [2, 27]⟩,
    ⟨.or, [11, 21]⟩,
    ⟨.and, [3, 29]⟩,
    ⟨.or, [15, 20]⟩,
    ⟨.and, [4, 31]⟩,
    ⟨.or, [8, 15]⟩,
    ⟨.or, [33, 19]⟩,
    ⟨.and, [5, 34]⟩,
    ⟨.or, [16, 18]⟩,
    ⟨.and, [6, 36]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.and, [7, 38]⟩,
    ⟨.or, [23, 26]⟩,
    ⟨.or, [40, 28]⟩,
    ⟨.or, [41, 30]⟩,
    ⟨.or, [42, 32]⟩,
    ⟨.or, [43, 35]⟩,
    ⟨.or, [44, 37]⟩,
    ⟨.or, [45, 39]⟩], 46⟩
  refine ⟨C, ?_, by decide, by decide +kernel⟩
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
