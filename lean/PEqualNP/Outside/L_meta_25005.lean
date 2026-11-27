import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25005

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 10]⟩,
      ⟨GateOp.or, [3, 15]⟩,
      ⟨GateOp.or, [4, 8]⟩,
      ⟨GateOp.or, [6, 11]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.or, [13, 18]⟩,
      ⟨GateOp.or, [22, 20]⟩,
      ⟨GateOp.or, [2, 9]⟩,
      ⟨GateOp.or, [1, 14]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.or, [26, 19]⟩,
      ⟨GateOp.or, [27, 20]⟩,
      ⟨GateOp.or, [5, 7]⟩,
      ⟨GateOp.or, [29, 12]⟩,
      ⟨GateOp.or, [30, 13]⟩,
      ⟨GateOp.or, [17, 21]⟩,
      ⟨GateOp.and, [16, 21]⟩,
      ⟨GateOp.and, [23, 24]⟩,
      ⟨GateOp.and, [5, 12]⟩,
      ⟨GateOp.and, [25, 28]⟩,
      ⟨GateOp.and, [31, 32]⟩,
      ⟨GateOp.or, [33, 34]⟩,
      ⟨GateOp.or, [38, 35]⟩,
      ⟨GateOp.or, [39, 36]⟩,
      ⟨GateOp.or, [40, 37]⟩
    ],
    output := 41 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_25005

theorem PEqualNP.Outside.L_meta_25005 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14516395958052687435 : ℕ).testBit (8 * u.val + v.val)) 26 :=
  ⟨PEqualNP.Outside.L_meta_25005.ckt, PEqualNP.Outside.L_meta_25005.mono, by decide, PEqualNP.Outside.L_meta_25005.rep⟩
