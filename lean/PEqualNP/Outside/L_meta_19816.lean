import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19816

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [9, 16]⟩,
      ⟨GateOp.or, [8, 17]⟩,
      ⟨GateOp.or, [21, 18]⟩,
      ⟨GateOp.and, [0, 22]⟩,
      ⟨GateOp.or, [18, 20]⟩,
      ⟨GateOp.and, [1, 24]⟩,
      ⟨GateOp.or, [17, 20]⟩,
      ⟨GateOp.and, [2, 26]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [28, 15]⟩,
      ⟨GateOp.or, [29, 18]⟩,
      ⟨GateOp.and, [3, 30]⟩,
      ⟨GateOp.or, [13, 16]⟩,
      ⟨GateOp.or, [32, 17]⟩,
      ⟨GateOp.and, [4, 33]⟩,
      ⟨GateOp.or, [10, 18]⟩,
      ⟨GateOp.or, [35, 19]⟩,
      ⟨GateOp.and, [5, 36]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [38, 19]⟩,
      ⟨GateOp.and, [6, 39]⟩,
      ⟨GateOp.or, [11, 17]⟩,
      ⟨GateOp.or, [41, 19]⟩,
      ⟨GateOp.and, [7, 42]⟩,
      ⟨GateOp.or, [23, 25]⟩,
      ⟨GateOp.or, [44, 27]⟩,
      ⟨GateOp.or, [45, 31]⟩,
      ⟨GateOp.or, [46, 34]⟩,
      ⟨GateOp.or, [47, 37]⟩,
      ⟨GateOp.or, [48, 40]⟩,
      ⟨GateOp.or, [49, 43]⟩
    ],
    output := 50 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (12570512712759991245 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19816

theorem PEqualNP.Outside.L_meta_19816 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12570512712759991245 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_meta_19816.ckt, PEqualNP.Outside.L_meta_19816.mono, by decide, PEqualNP.Outside.L_meta_19816.rep⟩
