import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19924

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.or, [9, 12]⟩,
      ⟨GateOp.or, [11, 15]⟩,
      ⟨GateOp.or, [13, 17]⟩,
      ⟨GateOp.and, [0, 19]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [21, 14]⟩,
      ⟨GateOp.and, [1, 22]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.and, [2, 24]⟩,
      ⟨GateOp.or, [11, 16]⟩,
      ⟨GateOp.and, [3, 26]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [28, 15]⟩,
      ⟨GateOp.and, [4, 29]⟩,
      ⟨GateOp.or, [9, 18]⟩,
      ⟨GateOp.and, [5, 31]⟩,
      ⟨GateOp.or, [8, 18]⟩,
      ⟨GateOp.and, [6, 33]⟩,
      ⟨GateOp.or, [14, 17]⟩,
      ⟨GateOp.and, [7, 35]⟩,
      ⟨GateOp.or, [20, 23]⟩,
      ⟨GateOp.or, [37, 25]⟩,
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

theorem rep : Represents (fun u v : Fin 8 => (5947437220121374770 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19924

theorem PEqualNP.Outside.L_meta_19924 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5947437220121374770 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19924.ckt, PEqualNP.Outside.L_meta_19924.mono, by decide, PEqualNP.Outside.L_meta_19924.rep⟩
