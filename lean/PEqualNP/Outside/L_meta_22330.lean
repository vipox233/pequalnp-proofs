import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22330

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.and, [0, 11]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.or, [8, 14]⟩,
      ⟨GateOp.or, [13, 7]⟩,
      ⟨GateOp.or, [15, 13]⟩,
      ⟨GateOp.or, [0, 16]⟩,
      ⟨GateOp.and, [10, 17]⟩,
      ⟨GateOp.or, [14, 12]⟩,
      ⟨GateOp.and, [18, 20]⟩,
      ⟨GateOp.or, [19, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841130 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22330

theorem PEqualNP.Outside.L_meta_22330 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841130 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22330.ckt, PEqualNP.Outside.L_meta_22330.mono, by decide, PEqualNP.Outside.L_meta_22330.rep⟩
