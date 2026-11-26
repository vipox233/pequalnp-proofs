import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22247

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 2]⟩,
      ⟨GateOp.and, [11, 6]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.or, [13, 5]⟩,
      ⟨GateOp.or, [4, 8]⟩,
      ⟨GateOp.or, [15, 9]⟩,
      ⟨GateOp.and, [16, 0]⟩,
      ⟨GateOp.or, [17, 12]⟩,
      ⟨GateOp.or, [2, 3]⟩,
      ⟨GateOp.or, [19, 7]⟩,
      ⟨GateOp.and, [20, 14]⟩,
      ⟨GateOp.or, [21, 18]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (815933 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22247

theorem PEqualNP.Outside.L_meta_22247 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (815933 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22247.ckt, PEqualNP.Outside.L_meta_22247.mono, by decide, PEqualNP.Outside.L_meta_22247.rep⟩
