import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22323

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [2, 1]⟩,
      ⟨GateOp.or, [1, 3]⟩,
      ⟨GateOp.or, [9, 8]⟩,
      ⟨GateOp.or, [6, 7]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [14, 5]⟩,
      ⟨GateOp.or, [12, 10]⟩,
      ⟨GateOp.or, [14, 13]⟩,
      ⟨GateOp.or, [11, 6]⟩,
      ⟨GateOp.and, [0, 18]⟩,
      ⟨GateOp.and, [16, 17]⟩,
      ⟨GateOp.and, [18, 15]⟩,
      ⟨GateOp.or, [21, 20]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (840692 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22323

theorem PEqualNP.Outside.L_meta_22323 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840692 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22323.ckt, PEqualNP.Outside.L_meta_22323.mono, by decide, PEqualNP.Outside.L_meta_22323.rep⟩
