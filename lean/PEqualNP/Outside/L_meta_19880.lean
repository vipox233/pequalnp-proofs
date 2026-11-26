import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19880_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [12, 15]⟩,
    ⟨GateOp.or, [8, 10]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [21, 14]⟩,
    ⟨GateOp.or, [22, 15]⟩,
    ⟨GateOp.and, [0, 23]⟩,
    ⟨GateOp.or, [8, 13]⟩,
    ⟨GateOp.or, [25, 16]⟩,
    ⟨GateOp.and, [1, 26]⟩,
    ⟨GateOp.or, [12, 14]⟩,
    ⟨GateOp.or, [28, 17]⟩,
    ⟨GateOp.and, [2, 29]⟩,
    ⟨GateOp.or, [11, 13]⟩,
    ⟨GateOp.or, [31, 17]⟩,
    ⟨GateOp.and, [3, 32]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.and, [4, 34]⟩,
    ⟨GateOp.or, [19, 20]⟩,
    ⟨GateOp.and, [5, 36]⟩,
    ⟨GateOp.or, [16, 19]⟩,
    ⟨GateOp.and, [6, 38]⟩,
    ⟨GateOp.or, [16, 18]⟩,
    ⟨GateOp.and, [7, 40]⟩,
    ⟨GateOp.or, [24, 27]⟩,
    ⟨GateOp.or, [42, 30]⟩,
    ⟨GateOp.or, [43, 33]⟩,
    ⟨GateOp.or, [44, 35]⟩,
    ⟨GateOp.or, [45, 37]⟩,
    ⟨GateOp.or, [46, 39]⟩,
    ⟨GateOp.or, [47, 41]⟩
    ]
    output := 48 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 33 := by decide +kernel

set_option maxRecDepth 40000 in
theorem C_rep : Represents (fun u v : Fin 8 => (10852103239182430665 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19880_aux

theorem PEqualNP.Outside.L_meta_19880 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10852103239182430665 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19880_aux.C, PEqualNP.Outside.L_meta_19880_aux.C_ok, PEqualNP.Outside.L_meta_19880_aux.C_size, PEqualNP.Outside.L_meta_19880_aux.C_rep⟩
