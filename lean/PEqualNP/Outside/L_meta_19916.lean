import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19916

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [8, 13]⟩,
      ⟨GateOp.or, [9, 11]⟩,
      ⟨GateOp.or, [10, 12]⟩,
      ⟨GateOp.or, [14, 15]⟩,
      ⟨GateOp.or, [11, 14]⟩,
      ⟨GateOp.or, [20, 18]⟩,
      ⟨GateOp.and, [0, 21]⟩,
      ⟨GateOp.or, [18, 19]⟩,
      ⟨GateOp.and, [1, 23]⟩,
      ⟨GateOp.or, [9, 13]⟩,
      ⟨GateOp.or, [25, 19]⟩,
      ⟨GateOp.and, [2, 26]⟩,
      ⟨GateOp.or, [16, 17]⟩,
      ⟨GateOp.and, [3, 28]⟩,
      ⟨GateOp.or, [16, 18]⟩,
      ⟨GateOp.and, [4, 30]⟩,
      ⟨GateOp.or, [8, 15]⟩,
      ⟨GateOp.or, [32, 17]⟩,
      ⟨GateOp.and, [5, 33]⟩,
      ⟨GateOp.or, [12, 14]⟩,
      ⟨GateOp.or, [35, 17]⟩,
      ⟨GateOp.and, [6, 36]⟩,
      ⟨GateOp.or, [10, 15]⟩,
      ⟨GateOp.or, [38, 16]⟩,
      ⟨GateOp.and, [7, 39]⟩,
      ⟨GateOp.or, [22, 24]⟩,
      ⟨GateOp.or, [41, 27]⟩,
      ⟨GateOp.or, [42, 29]⟩,
      ⟨GateOp.or, [43, 31]⟩,
      ⟨GateOp.or, [44, 34]⟩,
      ⟨GateOp.or, [45, 37]⟩,
      ⟨GateOp.or, [46, 40]⟩
    ],
    output := 47 }

theorem mono : Monotone2 ckt := by
  intro g hg
  simp only [ckt, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

theorem rep : Represents (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_19916

theorem PEqualNP.Outside.L_meta_19916 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19916.ckt, PEqualNP.Outside.L_meta_19916.mono, by decide, PEqualNP.Outside.L_meta_19916.rep⟩
