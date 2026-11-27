import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22542

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 7]⟩,
      ⟨GateOp.or, [9, 3]⟩,
      ⟨GateOp.or, [6, 1]⟩,
      ⟨GateOp.or, [11, 7]⟩,
      ⟨GateOp.or, [13, 12]⟩,
      ⟨GateOp.or, [0, 5]⟩,
      ⟨GateOp.and, [2, 10]⟩,
      ⟨GateOp.and, [15, 14]⟩,
      ⟨GateOp.or, [16, 4]⟩,
      ⟨GateOp.or, [18, 6]⟩,
      ⟨GateOp.or, [17, 18]⟩,
      ⟨GateOp.and, [13, 12]⟩,
      ⟨GateOp.or, [20, 21]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1940205 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22542

theorem PEqualNP.Outside.L_meta_22542 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940205 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22542.ckt, PEqualNP.Outside.L_meta_22542.mono, by decide, PEqualNP.Outside.L_meta_22542.rep⟩
