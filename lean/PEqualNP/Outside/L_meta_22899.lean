import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22899_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.or, [2, 9]⟩,
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [6, 2]⟩,
    ⟨GateOp.or, [11, 3]⟩,
    ⟨GateOp.or, [8, 14]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [7, 14]⟩,
    ⟨GateOp.or, [12, 1]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.or, [1, 16]⟩,
    ⟨GateOp.and, [19, 20]⟩,
    ⟨GateOp.or, [5, 18]⟩,
    ⟨GateOp.and, [17, 22]⟩,
    ⟨GateOp.or, [21, 23]⟩
    ]
    output := 24 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 15 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 6) => (1948536 : ℕ).testBit (6 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_22899_aux

theorem PEqualNP.Outside.L_meta_22899 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1948536 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨PEqualNP.Outside.L_meta_22899_aux.C, PEqualNP.Outside.L_meta_22899_aux.C_ok, PEqualNP.Outside.L_meta_22899_aux.C_size, PEqualNP.Outside.L_meta_22899_aux.C_rep⟩
