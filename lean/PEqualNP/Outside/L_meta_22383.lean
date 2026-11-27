import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22383

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [9, 6]⟩,
      ⟨GateOp.or, [8, 3]⟩,
      ⟨GateOp.or, [2, 0]⟩,
      ⟨GateOp.or, [10, 1]⟩,
      ⟨GateOp.or, [14, 5]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.and, [17, 2]⟩,
      ⟨GateOp.and, [16, 15]⟩,
      ⟨GateOp.and, [13, 4]⟩,
      ⟨GateOp.or, [19, 20]⟩,
      ⟨GateOp.or, [18, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843061 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22383

theorem PEqualNP.Outside.L_meta_22383 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843061 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22383.ckt, PEqualNP.Outside.L_meta_22383.mono, by decide, PEqualNP.Outside.L_meta_22383.rep⟩
