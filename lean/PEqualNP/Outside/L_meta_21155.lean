import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21155_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [7, 2]⟩,
    ⟨GateOp.or, [10, 8]⟩,
    ⟨GateOp.or, [1, 6]⟩,
    ⟨GateOp.and, [11, 12]⟩,
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [12, 11]⟩,
    ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [9, 16]⟩,
    ⟨GateOp.or, [13, 17]⟩
    ]
    output := 18 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 10 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (39772 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21155_aux

theorem PEqualNP.Outside.L_meta_21155 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39772 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨PEqualNP.Outside.L_meta_21155_aux.C, PEqualNP.Outside.L_meta_21155_aux.C_ok, PEqualNP.Outside.L_meta_21155_aux.C_size, PEqualNP.Outside.L_meta_21155_aux.C_rep⟩
