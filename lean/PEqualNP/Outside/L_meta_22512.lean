import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22512

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 3]⟩,
      ⟨GateOp.or, [1, 6]⟩,
      ⟨GateOp.and, [7, 2]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.or, [11, 12]⟩,
      ⟨GateOp.or, [9, 2]⟩,
      ⟨GateOp.or, [13, 14]⟩,
      ⟨GateOp.and, [11, 13]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.and, [4, 13]⟩,
      ⟨GateOp.or, [4, 17]⟩,
      ⟨GateOp.and, [18, 16]⟩,
      ⟨GateOp.or, [20, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1899765 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22512

theorem PEqualNP.Outside.L_meta_22512 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1899765 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22512.ckt, PEqualNP.Outside.L_meta_22512.mono, by decide, PEqualNP.Outside.L_meta_22512.rep⟩
