import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19754_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit :=
  { gates := [
    ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.and, [0, 19]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [21, 14]⟩, ⟨GateOp.and, [1, 22]⟩, ⟨GateOp.or, [10, 17]⟩, ⟨GateOp.and, [2, 24]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [26, 15]⟩, ⟨GateOp.and, [3, 27]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [4, 29]⟩, ⟨GateOp.or, [10, 18]⟩, ⟨GateOp.and, [5, 31]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.and, [6, 33]⟩, ⟨GateOp.or, [12, 18]⟩, ⟨GateOp.and, [7, 35]⟩, ⟨GateOp.or, [20, 23]⟩, ⟨GateOp.or, [37, 25]⟩, ⟨GateOp.or, [38, 28]⟩, ⟨GateOp.or, [39, 30]⟩, ⟨GateOp.or, [40, 32]⟩, ⟨GateOp.or, [41, 34]⟩, ⟨GateOp.or, [42, 36]⟩
    ]
    output := 43 }

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem C_size : C.size ≤ 28 := by decide

theorem C_rep : Represents (fun u v : Fin 8 => (14991291321697978680 : ℕ).testBit (8 * u.val + v.val)) C := by
  intro u v
  revert u v
  decide

end PEqualNP.Outside.L_meta_19754_aux

theorem PEqualNP.Outside.L_meta_19754 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14991291321697978680 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19754_aux.C, PEqualNP.Outside.L_meta_19754_aux.C_mono, PEqualNP.Outside.L_meta_19754_aux.C_size, PEqualNP.Outside.L_meta_19754_aux.C_rep⟩
