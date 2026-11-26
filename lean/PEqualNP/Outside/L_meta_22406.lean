import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22406

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 5]⟩,
      ⟨GateOp.or, [10, 0]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [2, 4]⟩,
      ⟨GateOp.or, [8, 1]⟩,
      ⟨GateOp.or, [7, 12]⟩,
      ⟨GateOp.or, [0, 13]⟩,
      ⟨GateOp.or, [15, 14]⟩,
      ⟨GateOp.and, [17, 16]⟩,
      ⟨GateOp.and, [8, 6]⟩,
      ⟨GateOp.or, [15, 9]⟩,
      ⟨GateOp.and, [11, 20]⟩,
      ⟨GateOp.or, [18, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (904060 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22406

theorem PEqualNP.Outside.L_meta_22406 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904060 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22406.ckt, PEqualNP.Outside.L_meta_22406.mono, by decide, PEqualNP.Outside.L_meta_22406.rep⟩
