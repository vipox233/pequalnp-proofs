import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19930

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [9, 15]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [14, 19]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.and, [0, 22]⟩,
      ⟨GateOp.or, [12, 21]⟩,
      ⟨GateOp.and, [1, 24]⟩,
      ⟨GateOp.or, [16, 20]⟩,
      ⟨GateOp.and, [2, 26]⟩,
      ⟨GateOp.or, [15, 21]⟩,
      ⟨GateOp.and, [3, 28]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [30, 17]⟩,
      ⟨GateOp.and, [4, 31]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.or, [33, 16]⟩,
      ⟨GateOp.and, [5, 34]⟩,
      ⟨GateOp.or, [16, 18]⟩,
      ⟨GateOp.and, [6, 36]⟩,
      ⟨GateOp.or, [17, 20]⟩,
      ⟨GateOp.and, [7, 38]⟩,
      ⟨GateOp.or, [23, 25]⟩,
      ⟨GateOp.or, [40, 27]⟩,
      ⟨GateOp.or, [41, 29]⟩,
      ⟨GateOp.or, [42, 32]⟩,
      ⟨GateOp.or, [43, 35]⟩,
      ⟨GateOp.or, [44, 37]⟩,
      ⟨GateOp.or, [45, 39]⟩
    ],
    output := 46 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (4361677255813263645 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19930

theorem PEqualNP.Outside.L_meta_19930 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (4361677255813263645 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19930.ckt, PEqualNP.Outside.L_meta_19930.mono, by decide, PEqualNP.Outside.L_meta_19930.rep⟩
