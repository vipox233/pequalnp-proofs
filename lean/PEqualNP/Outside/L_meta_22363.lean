import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22363

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 1]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [9, 2]⟩,
      ⟨GateOp.or, [13, 5]⟩,
      ⟨GateOp.or, [12, 5]⟩,
      ⟨GateOp.and, [12, 14]⟩,
      ⟨GateOp.or, [15, 1]⟩,
      ⟨GateOp.or, [8, 3]⟩,
      ⟨GateOp.and, [18, 17]⟩,
      ⟨GateOp.and, [11, 10]⟩,
      ⟨GateOp.or, [20, 19]⟩,
      ⟨GateOp.or, [21, 16]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841522 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22363

theorem PEqualNP.Outside.L_meta_22363 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841522 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22363.ckt, PEqualNP.Outside.L_meta_22363.mono, by decide, PEqualNP.Outside.L_meta_22363.rep⟩
