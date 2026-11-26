import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21157

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 2]⟩,
      ⟨GateOp.or, [0, 4]⟩,
      ⟨GateOp.or, [5, 6]⟩,
      ⟨GateOp.or, [7, 9]⟩,
      ⟨GateOp.or, [3, 11]⟩,
      ⟨GateOp.and, [9, 13]⟩,
      ⟨GateOp.or, [12, 13]⟩,
      ⟨GateOp.or, [8, 15]⟩,
      ⟨GateOp.and, [10, 16]⟩,
      ⟨GateOp.or, [14, 17]⟩
    ],
    output := 18 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun (u : Fin 4) (v : Fin 5) => (40190 : ℕ).testBit (5 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_21157

theorem PEqualNP.Outside.L_meta_21157 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40190 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_21157.ckt, PEqualNP.Outside.L_meta_21157.mono, by decide, PEqualNP.Outside.L_meta_21157.rep⟩
