import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19825

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [12, 17]⟩,
      ⟨GateOp.and, [0, 19]⟩,
      ⟨GateOp.or, [11, 17]⟩,
      ⟨GateOp.and, [1, 21]⟩,
      ⟨GateOp.or, [8, 18]⟩,
      ⟨GateOp.and, [2, 23]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [25, 14]⟩,
      ⟨GateOp.and, [3, 26]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [28, 15]⟩,
      ⟨GateOp.and, [4, 29]⟩,
      ⟨GateOp.or, [10, 16]⟩,
      ⟨GateOp.and, [5, 31]⟩,
      ⟨GateOp.or, [13, 18]⟩,
      ⟨GateOp.and, [6, 33]⟩,
      ⟨GateOp.or, [12, 16]⟩,
      ⟨GateOp.and, [7, 35]⟩,
      ⟨GateOp.or, [20, 22]⟩,
      ⟨GateOp.or, [37, 24]⟩,
      ⟨GateOp.or, [38, 27]⟩,
      ⟨GateOp.or, [39, 30]⟩,
      ⟨GateOp.or, [40, 32]⟩,
      ⟨GateOp.or, [41, 34]⟩,
      ⟨GateOp.or, [42, 36]⟩
    ],
    output := 43 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (1432153032174414900 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19825

theorem PEqualNP.Outside.L_meta_19825 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1432153032174414900 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19825.ckt, PEqualNP.Outside.L_meta_19825.mono, by decide, PEqualNP.Outside.L_meta_19825.rep⟩
