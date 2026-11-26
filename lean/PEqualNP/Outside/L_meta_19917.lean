import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19917

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [10, 17]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [15, 18]⟩,
      ⟨GateOp.or, [12, 17]⟩,
      ⟨GateOp.or, [23, 19]⟩,
      ⟨GateOp.and, [0, 24]⟩,
      ⟨GateOp.or, [19, 20]⟩,
      ⟨GateOp.and, [1, 26]⟩,
      ⟨GateOp.or, [16, 22]⟩,
      ⟨GateOp.and, [2, 28]⟩,
      ⟨GateOp.or, [16, 20]⟩,
      ⟨GateOp.and, [3, 30]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.or, [32, 21]⟩,
      ⟨GateOp.and, [4, 33]⟩,
      ⟨GateOp.or, [18, 21]⟩,
      ⟨GateOp.and, [5, 35]⟩,
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [37, 13]⟩,
      ⟨GateOp.or, [38, 19]⟩,
      ⟨GateOp.and, [6, 39]⟩,
      ⟨GateOp.or, [17, 22]⟩,
      ⟨GateOp.and, [7, 41]⟩,
      ⟨GateOp.or, [25, 27]⟩,
      ⟨GateOp.or, [43, 29]⟩,
      ⟨GateOp.or, [44, 31]⟩,
      ⟨GateOp.or, [45, 34]⟩,
      ⟨GateOp.or, [46, 36]⟩,
      ⟨GateOp.or, [47, 40]⟩,
      ⟨GateOp.or, [48, 42]⟩
    ],
    output := 49 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19917

theorem PEqualNP.Outside.L_meta_19917 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19917.ckt, PEqualNP.Outside.L_meta_19917.mono, by decide, PEqualNP.Outside.L_meta_19917.rep⟩
