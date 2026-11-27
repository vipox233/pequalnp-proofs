import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22510

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [4, 0]⟩,
      ⟨GateOp.or, [9, 3]⟩,
      ⟨GateOp.or, [3, 7]⟩,
      ⟨GateOp.or, [1, 10]⟩,
      ⟨GateOp.and, [14, 11]⟩,
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.or, [15, 16]⟩,
      ⟨GateOp.and, [7, 2]⟩,
      ⟨GateOp.or, [18, 14]⟩,
      ⟨GateOp.or, [12, 17]⟩,
      ⟨GateOp.or, [19, 11]⟩,
      ⟨GateOp.and, [21, 20]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1899638 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22510

theorem PEqualNP.Outside.L_meta_22510 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899638 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22510.ckt, PEqualNP.Outside.L_meta_22510.mono, by decide, PEqualNP.Outside.L_meta_22510.rep⟩
