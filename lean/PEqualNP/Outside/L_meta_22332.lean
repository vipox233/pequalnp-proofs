import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22332

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [6, 3]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.or, [10, 7]⟩,
      ⟨GateOp.or, [0, 12]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [8, 12]⟩,
      ⟨GateOp.or, [16, 11]⟩,
      ⟨GateOp.and, [17, 15]⟩,
      ⟨GateOp.or, [11, 13]⟩,
      ⟨GateOp.and, [19, 14]⟩,
      ⟨GateOp.or, [15, 7]⟩,
      ⟨GateOp.or, [20, 18]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841132 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22332

theorem PEqualNP.Outside.L_meta_22332 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841132 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22332.ckt, PEqualNP.Outside.L_meta_22332.mono, by decide, PEqualNP.Outside.L_meta_22332.rep⟩
