import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21273

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [1, 6]⟩,
      ⟨GateOp.or, [2, 7]⟩,
      ⟨GateOp.or, [10, 11]⟩,
      ⟨GateOp.or, [4, 8]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.and, [9, 14]⟩,
      ⟨GateOp.and, [3, 4]⟩,
      ⟨GateOp.and, [11, 10]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.or, [18, 17]⟩
    ],
    output := 19 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (39261 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21273

theorem PEqualNP.Outside.L_meta_21273 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39261 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨PEqualNP.Outside.L_meta_21273.ckt, PEqualNP.Outside.L_meta_21273.mono, by decide, PEqualNP.Outside.L_meta_21273.rep⟩
