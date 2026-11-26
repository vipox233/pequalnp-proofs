import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22126

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [9, 3]⟩,
      ⟨GateOp.or, [6, 8]⟩,
      ⟨GateOp.or, [4, 0]⟩,
      ⟨GateOp.or, [11, 10]⟩,
      ⟨GateOp.or, [5, 12]⟩,
      ⟨GateOp.and, [13, 14]⟩,
      ⟨GateOp.or, [7, 6]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.and, [1, 17]⟩,
      ⟨GateOp.or, [15, 18]⟩,
      ⟨GateOp.and, [16, 2]⟩,
      ⟨GateOp.or, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (837108 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22126

theorem PEqualNP.Outside.L_meta_22126 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837108 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22126.ckt, PEqualNP.Outside.L_meta_22126.mono, by decide, PEqualNP.Outside.L_meta_22126.rep⟩
