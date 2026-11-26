import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22169

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 7]⟩,
      ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [12, 2]⟩,
      ⟨GateOp.or, [13, 5]⟩,
      ⟨GateOp.or, [14, 1]⟩,
      ⟨GateOp.or, [14, 8]⟩,
      ⟨GateOp.and, [16, 11]⟩,
      ⟨GateOp.or, [17, 4]⟩,
      ⟨GateOp.or, [3, 6]⟩,
      ⟨GateOp.and, [19, 15]⟩,
      ⟨GateOp.or, [20, 18]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841203 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22169

theorem PEqualNP.Outside.L_meta_22169 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841203 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22169.ckt, PEqualNP.Outside.L_meta_22169.mono, by decide, PEqualNP.Outside.L_meta_22169.rep⟩
