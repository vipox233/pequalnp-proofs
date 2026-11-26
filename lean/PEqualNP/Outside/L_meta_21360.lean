import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21360_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.and, [3, 4]⟩,
    ⟨GateOp.or, [7, 4]⟩,
    ⟨GateOp.or, [9, 1]⟩,
    ⟨GateOp.or, [2, 10]⟩,
    ⟨GateOp.or, [11, 6]⟩,
    ⟨GateOp.or, [12, 13]⟩,
    ⟨GateOp.and, [12, 13]⟩,
    ⟨GateOp.and, [8, 15]⟩,
    ⟨GateOp.or, [15, 0]⟩,
    ⟨GateOp.or, [17, 5]⟩,
    ⟨GateOp.or, [8, 14]⟩,
    ⟨GateOp.and, [18, 19]⟩
    ]
    output := 20 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 12 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (39293 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21360_aux

theorem PEqualNP.Outside.L_meta_21360 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39293 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_21360_aux.C, PEqualNP.Outside.L_meta_21360_aux.C_ok, PEqualNP.Outside.L_meta_21360_aux.C_size, PEqualNP.Outside.L_meta_21360_aux.C_rep⟩
