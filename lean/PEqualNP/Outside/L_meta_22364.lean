import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22364

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.or, [5, 4]⟩,
      ⟨GateOp.or, [10, 9]⟩,
      ⟨GateOp.or, [0, 3]⟩,
      ⟨GateOp.or, [7, 6]⟩,
      ⟨GateOp.or, [8, 14]⟩,
      ⟨GateOp.or, [4, 0]⟩,
      ⟨GateOp.and, [1, 15]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.and, [11, 13]⟩,
      ⟨GateOp.or, [17, 19]⟩,
      ⟨GateOp.and, [12, 18]⟩,
      ⟨GateOp.or, [20, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841523 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22364

theorem PEqualNP.Outside.L_meta_22364 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841523 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22364.ckt, PEqualNP.Outside.L_meta_22364.mono, by decide, PEqualNP.Outside.L_meta_22364.rep⟩
