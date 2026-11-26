import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19913

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [14, 18]⟩,
      ⟨GateOp.or, [15, 17]⟩,
      ⟨GateOp.or, [8, 15]⟩,
      ⟨GateOp.or, [22, 20]⟩,
      ⟨GateOp.and, [0, 23]⟩,
      ⟨GateOp.or, [17, 19]⟩,
      ⟨GateOp.and, [1, 25]⟩,
      ⟨GateOp.or, [18, 21]⟩,
      ⟨GateOp.and, [2, 27]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.and, [3, 29]⟩,
      ⟨GateOp.or, [11, 15]⟩,
      ⟨GateOp.or, [31, 19]⟩,
      ⟨GateOp.and, [4, 32]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [34, 21]⟩,
      ⟨GateOp.and, [5, 35]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [37, 15]⟩,
      ⟨GateOp.or, [38, 16]⟩,
      ⟨GateOp.and, [6, 39]⟩,
      ⟨GateOp.or, [17, 20]⟩,
      ⟨GateOp.and, [7, 41]⟩,
      ⟨GateOp.or, [24, 26]⟩,
      ⟨GateOp.or, [43, 28]⟩,
      ⟨GateOp.or, [44, 30]⟩,
      ⟨GateOp.or, [45, 33]⟩,
      ⟨GateOp.or, [46, 36]⟩,
      ⟨GateOp.or, [47, 40]⟩,
      ⟨GateOp.or, [48, 42]⟩
    ],
    output := 49 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (8982322578471014385 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19913

theorem PEqualNP.Outside.L_meta_19913 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8982322578471014385 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19913.ckt, PEqualNP.Outside.L_meta_19913.mono, by decide, PEqualNP.Outside.L_meta_19913.rep⟩
