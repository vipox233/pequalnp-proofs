import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21405_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [1, 3]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [10, 0]⟩,
    ⟨GateOp.and, [7, 1]⟩,
    ⟨GateOp.or, [6, 2]⟩,
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [14, 8]⟩,
    ⟨GateOp.or, [13, 12]⟩,
    ⟨GateOp.or, [16, 15]⟩,
    ⟨GateOp.and, [14, 16]⟩,
    ⟨GateOp.and, [11, 17]⟩,
    ⟨GateOp.or, [18, 19]⟩
    ]
    output := 20 }

theorem C_ok : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 12 := by decide +kernel

set_option maxRecDepth 20000 in
theorem C_rep : Represents (fun (u : Fin 4) (v : Fin 5) => (241148 : ℕ).testBit (5 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_21405_aux

theorem PEqualNP.Outside.L_meta_21405 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241148 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  ⟨PEqualNP.Outside.L_meta_21405_aux.C, PEqualNP.Outside.L_meta_21405_aux.C_ok, PEqualNP.Outside.L_meta_21405_aux.C_size, PEqualNP.Outside.L_meta_21405_aux.C_rep⟩
