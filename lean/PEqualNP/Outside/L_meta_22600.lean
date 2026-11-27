import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22600

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 2]⟩,
      ⟨GateOp.or, [10, 6]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [13, 0]⟩,
      ⟨GateOp.or, [13, 9]⟩,
      ⟨GateOp.and, [15, 12]⟩,
      ⟨GateOp.or, [4, 5]⟩,
      ⟨GateOp.and, [17, 14]⟩,
      ⟨GateOp.or, [18, 16]⟩,
      ⟨GateOp.or, [7, 8]⟩,
      ⟨GateOp.and, [20, 11]⟩,
      ⟨GateOp.or, [21, 19]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1965627 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22600

theorem PEqualNP.Outside.L_meta_22600 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965627 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22600.ckt, PEqualNP.Outside.L_meta_22600.mono, by decide, PEqualNP.Outside.L_meta_22600.rep⟩
