import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22183

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [1, 4]⟩,
      ⟨GateOp.or, [8, 2]⟩,
      ⟨GateOp.and, [12, 11]⟩,
      ⟨GateOp.or, [5, 2]⟩,
      ⟨GateOp.or, [14, 11]⟩,
      ⟨GateOp.or, [13, 3]⟩,
      ⟨GateOp.or, [16, 6]⟩,
      ⟨GateOp.or, [17, 7]⟩,
      ⟨GateOp.or, [10, 18]⟩,
      ⟨GateOp.or, [15, 0]⟩,
      ⟨GateOp.and, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841516 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22183

theorem PEqualNP.Outside.L_meta_22183 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841516 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22183.ckt, PEqualNP.Outside.L_meta_22183.mono, by decide, PEqualNP.Outside.L_meta_22183.rep⟩
