import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19935

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [9, 15]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [12, 18]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.and, [0, 21]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.or, [23, 17]⟩,
      ⟨GateOp.and, [1, 24]⟩,
      ⟨GateOp.or, [15, 19]⟩,
      ⟨GateOp.and, [2, 26]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [28, 17]⟩,
      ⟨GateOp.and, [3, 29]⟩,
      ⟨GateOp.or, [9, 19]⟩,
      ⟨GateOp.and, [4, 31]⟩,
      ⟨GateOp.or, [11, 20]⟩,
      ⟨GateOp.and, [5, 33]⟩,
      ⟨GateOp.or, [8, 14]⟩,
      ⟨GateOp.or, [35, 18]⟩,
      ⟨GateOp.and, [6, 36]⟩,
      ⟨GateOp.or, [12, 20]⟩,
      ⟨GateOp.and, [7, 38]⟩,
      ⟨GateOp.or, [22, 25]⟩,
      ⟨GateOp.or, [40, 27]⟩,
      ⟨GateOp.or, [41, 30]⟩,
      ⟨GateOp.or, [42, 32]⟩,
      ⟨GateOp.or, [43, 34]⟩,
      ⟨GateOp.or, [44, 37]⟩,
      ⟨GateOp.or, [45, 39]⟩
    ],
    output := 46 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (8164297279589376675 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19935

theorem PEqualNP.Outside.L_meta_19935 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8164297279589376675 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19935.ckt, PEqualNP.Outside.L_meta_19935.mono, by decide, PEqualNP.Outside.L_meta_19935.rep⟩
