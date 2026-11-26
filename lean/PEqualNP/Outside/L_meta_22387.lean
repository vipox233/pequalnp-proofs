import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22387

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [4, 0]⟩,
      ⟨GateOp.or, [10, 1]⟩,
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.or, [12, 6]⟩,
      ⟨GateOp.or, [13, 9]⟩,
      ⟨GateOp.and, [11, 14]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.or, [16, 10]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.or, [7, 18]⟩,
      ⟨GateOp.and, [17, 19]⟩,
      ⟨GateOp.and, [3, 2]⟩,
      ⟨GateOp.or, [20, 15]⟩
    ],
    output := 22 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (843068 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22387

theorem PEqualNP.Outside.L_meta_22387 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (843068 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_22387.ckt, PEqualNP.Outside.L_meta_22387.mono, by decide, PEqualNP.Outside.L_meta_22387.rep⟩
