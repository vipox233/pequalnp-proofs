import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19836

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 9]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [10, 16]⟩,
      ⟨GateOp.and, [0, 18]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [20, 15]⟩,
      ⟨GateOp.and, [1, 21]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [23, 13]⟩,
      ⟨GateOp.and, [2, 24]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [26, 13]⟩,
      ⟨GateOp.and, [3, 27]⟩,
      ⟨GateOp.or, [8, 11]⟩,
      ⟨GateOp.or, [29, 14]⟩,
      ⟨GateOp.and, [4, 30]⟩,
      ⟨GateOp.or, [12, 17]⟩,
      ⟨GateOp.and, [5, 32]⟩,
      ⟨GateOp.or, [12, 16]⟩,
      ⟨GateOp.and, [6, 34]⟩,
      ⟨GateOp.or, [13, 17]⟩,
      ⟨GateOp.and, [7, 36]⟩,
      ⟨GateOp.or, [19, 22]⟩,
      ⟨GateOp.or, [38, 25]⟩,
      ⟨GateOp.or, [39, 28]⟩,
      ⟨GateOp.or, [40, 31]⟩,
      ⟨GateOp.or, [41, 33]⟩,
      ⟨GateOp.or, [42, 35]⟩,
      ⟨GateOp.or, [43, 37]⟩
    ],
    output := 44 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (16146478101879753735 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19836

theorem PEqualNP.Outside.L_meta_19836 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16146478101879753735 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_meta_19836.ckt, PEqualNP.Outside.L_meta_19836.mono, by decide, PEqualNP.Outside.L_meta_19836.rep⟩
