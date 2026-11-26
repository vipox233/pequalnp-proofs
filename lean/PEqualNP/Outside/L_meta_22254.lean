import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22254

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [5, 10]⟩,
      ⟨GateOp.or, [8, 7]⟩,
      ⟨GateOp.or, [6, 1]⟩,
      ⟨GateOp.or, [12, 2]⟩,
      ⟨GateOp.or, [3, 9]⟩,
      ⟨GateOp.and, [10, 13]⟩,
      ⟨GateOp.and, [14, 13]⟩,
      ⟨GateOp.or, [15, 14]⟩,
      ⟨GateOp.or, [8, 10]⟩,
      ⟨GateOp.and, [11, 18]⟩,
      ⟨GateOp.or, [20, 17]⟩,
      ⟨GateOp.or, [16, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (816764 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22254

theorem PEqualNP.Outside.L_meta_22254 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (816764 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22254.ckt, PEqualNP.Outside.L_meta_22254.mono, by decide, PEqualNP.Outside.L_meta_22254.rep⟩
