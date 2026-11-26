import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22288

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.or, [5, 0]⟩,
      ⟨GateOp.or, [8, 6]⟩,
      ⟨GateOp.or, [12, 10]⟩,
      ⟨GateOp.or, [11, 1]⟩,
      ⟨GateOp.or, [7, 15]⟩,
      ⟨GateOp.and, [16, 14]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [9, 18]⟩,
      ⟨GateOp.or, [13, 0]⟩,
      ⟨GateOp.and, [19, 20]⟩,
      ⟨GateOp.or, [17, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (837101 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22288

theorem PEqualNP.Outside.L_meta_22288 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837101 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22288.ckt, PEqualNP.Outside.L_meta_22288.mono, by decide, PEqualNP.Outside.L_meta_22288.rep⟩
