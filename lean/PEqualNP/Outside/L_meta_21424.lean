import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21424_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.or, [4, 0]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [12, 3]⟩,
    ⟨GateOp.or, [9, 10]⟩,
    ⟨GateOp.or, [7, 10]⟩,
    ⟨GateOp.or, [7, 3]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.and, [15, 11]⟩,
    ⟨GateOp.and, [16, 12]⟩,
    ⟨GateOp.or, [17, 18]⟩,
    ⟨GateOp.or, [19, 20]⟩
    ]
    output := 21 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 13 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (241078 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21424_aux

theorem PEqualNP.Outside.L_meta_21424 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241078 : ℕ).testBit (5 * u.val + v.val)) 13 :=
  ⟨PEqualNP.Outside.L_meta_21424_aux.C, PEqualNP.Outside.L_meta_21424_aux.C_ok, PEqualNP.Outside.L_meta_21424_aux.C_size, PEqualNP.Outside.L_meta_21424_aux.C_rep⟩
