import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19796

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [18, 13]⟩,
      ⟨GateOp.and, [0, 19]⟩,
      ⟨GateOp.or, [9, 10]⟩,
      ⟨GateOp.or, [21, 15]⟩,
      ⟨GateOp.and, [1, 22]⟩,
      ⟨GateOp.or, [9, 16]⟩,
      ⟨GateOp.and, [2, 24]⟩,
      ⟨GateOp.or, [10, 17]⟩,
      ⟨GateOp.and, [3, 26]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [28, 14]⟩,
      ⟨GateOp.and, [4, 29]⟩,
      ⟨GateOp.or, [12, 16]⟩,
      ⟨GateOp.and, [5, 31]⟩,
      ⟨GateOp.or, [15, 17]⟩,
      ⟨GateOp.and, [6, 33]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [35, 15]⟩,
      ⟨GateOp.and, [7, 36]⟩,
      ⟨GateOp.or, [20, 23]⟩,
      ⟨GateOp.or, [38, 25]⟩,
      ⟨GateOp.or, [39, 27]⟩,
      ⟨GateOp.or, [40, 30]⟩,
      ⟨GateOp.or, [41, 32]⟩,
      ⟨GateOp.or, [42, 34]⟩,
      ⟨GateOp.or, [43, 37]⟩
    ],
    output := 44 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (9928239608072734260 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19796

theorem PEqualNP.Outside.L_meta_19796 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9928239608072734260 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_meta_19796.ckt, PEqualNP.Outside.L_meta_19796.mono, by decide, PEqualNP.Outside.L_meta_19796.rep⟩
