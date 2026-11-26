import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22185

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [0, 1]⟩,
      ⟨GateOp.or, [10, 4]⟩,
      ⟨GateOp.or, [11, 2]⟩,
      ⟨GateOp.or, [12, 5]⟩,
      ⟨GateOp.or, [2, 8]⟩,
      ⟨GateOp.and, [14, 11]⟩,
      ⟨GateOp.or, [15, 3]⟩,
      ⟨GateOp.or, [16, 6]⟩,
      ⟨GateOp.or, [17, 7]⟩,
      ⟨GateOp.and, [18, 13]⟩,
      ⟨GateOp.and, [0, 9]⟩,
      ⟨GateOp.or, [20, 19]⟩
    ],
    output := 21 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : Represents (fun (u : Fin 4) (v : Fin 6) => (841532 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_22185

theorem PEqualNP.Outside.L_meta_22185 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841532 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_22185.ckt, PEqualNP.Outside.L_meta_22185.mono, by decide, PEqualNP.Outside.L_meta_22185.rep⟩
