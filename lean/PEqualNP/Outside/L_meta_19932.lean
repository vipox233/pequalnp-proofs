import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19932

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [13, 15]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [9, 14]⟩,
      ⟨GateOp.or, [17, 19]⟩,
      ⟨GateOp.and, [0, 20]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.and, [1, 22]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [24, 19]⟩,
      ⟨GateOp.and, [2, 25]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [27, 16]⟩,
      ⟨GateOp.and, [3, 28]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.or, [30, 16]⟩,
      ⟨GateOp.and, [4, 31]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [33, 12]⟩,
      ⟨GateOp.or, [34, 15]⟩,
      ⟨GateOp.and, [5, 35]⟩,
      ⟨GateOp.or, [16, 18]⟩,
      ⟨GateOp.and, [6, 37]⟩,
      ⟨GateOp.or, [10, 14]⟩,
      ⟨GateOp.or, [39, 17]⟩,
      ⟨GateOp.and, [7, 40]⟩,
      ⟨GateOp.or, [21, 23]⟩,
      ⟨GateOp.or, [42, 26]⟩,
      ⟨GateOp.or, [43, 29]⟩,
      ⟨GateOp.or, [44, 32]⟩,
      ⟨GateOp.or, [45, 36]⟩,
      ⟨GateOp.or, [46, 38]⟩,
      ⟨GateOp.or, [47, 41]⟩
    ],
    output := 48 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (16436895475263517410 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19932

theorem PEqualNP.Outside.L_meta_19932 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16436895475263517410 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19932.ckt, PEqualNP.Outside.L_meta_19932.mono, by decide, PEqualNP.Outside.L_meta_19932.rep⟩
