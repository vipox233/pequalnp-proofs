import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19920

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [14, 19]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.or, [21, 17]⟩,
      ⟨GateOp.and, [0, 22]⟩,
      ⟨GateOp.or, [10, 13]⟩,
      ⟨GateOp.or, [24, 16]⟩,
      ⟨GateOp.and, [1, 25]⟩,
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [27, 17]⟩,
      ⟨GateOp.and, [2, 28]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [30, 16]⟩,
      ⟨GateOp.and, [3, 31]⟩,
      ⟨GateOp.or, [9, 20]⟩,
      ⟨GateOp.and, [4, 33]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.and, [5, 35]⟩,
      ⟨GateOp.or, [16, 18]⟩,
      ⟨GateOp.and, [6, 37]⟩,
      ⟨GateOp.or, [15, 20]⟩,
      ⟨GateOp.and, [7, 39]⟩,
      ⟨GateOp.or, [23, 26]⟩,
      ⟨GateOp.or, [41, 29]⟩,
      ⟨GateOp.or, [42, 32]⟩,
      ⟨GateOp.or, [43, 34]⟩,
      ⟨GateOp.or, [44, 36]⟩,
      ⟨GateOp.or, [45, 38]⟩,
      ⟨GateOp.or, [46, 40]⟩
    ],
    output := 47 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (17315157982817101740 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19920

theorem PEqualNP.Outside.L_meta_19920 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17315157982817101740 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19920.ckt, PEqualNP.Outside.L_meta_19920.mono, by decide, PEqualNP.Outside.L_meta_19920.rep⟩
