import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19925

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [8, 14]⟩,
      ⟨GateOp.or, [13, 16]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [21, 19]⟩,
      ⟨GateOp.and, [0, 22]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.and, [1, 24]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [26, 17]⟩,
      ⟨GateOp.and, [2, 27]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.and, [3, 29]⟩,
      ⟨GateOp.or, [9, 15]⟩,
      ⟨GateOp.or, [31, 18]⟩,
      ⟨GateOp.and, [4, 32]⟩,
      ⟨GateOp.or, [14, 20]⟩,
      ⟨GateOp.and, [5, 34]⟩,
      ⟨GateOp.or, [15, 20]⟩,
      ⟨GateOp.and, [6, 36]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.or, [38, 19]⟩,
      ⟨GateOp.and, [7, 39]⟩,
      ⟨GateOp.or, [23, 25]⟩,
      ⟨GateOp.or, [41, 28]⟩,
      ⟨GateOp.or, [42, 30]⟩,
      ⟨GateOp.or, [43, 33]⟩,
      ⟨GateOp.or, [44, 35]⟩,
      ⟨GateOp.or, [45, 37]⟩,
      ⟨GateOp.or, [46, 40]⟩
    ],
    output := 47 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19925

theorem PEqualNP.Outside.L_meta_19925 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19925.ckt, PEqualNP.Outside.L_meta_19925.mono, by decide, PEqualNP.Outside.L_meta_19925.rep⟩
