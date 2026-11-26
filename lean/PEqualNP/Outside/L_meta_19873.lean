import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19873_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[⟨GateOp.or, [8, 15]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.and, [0, 21]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [23, 18]⟩, ⟨GateOp.and, [1, 24]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [26, 17]⟩, ⟨GateOp.and, [2, 27]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [29, 16]⟩, ⟨GateOp.and, [3, 30]⟩, ⟨GateOp.or, [15, 20]⟩, ⟨GateOp.and, [4, 32]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.and, [5, 34]⟩, ⟨GateOp.or, [10, 20]⟩, ⟨GateOp.and, [6, 36]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.and, [7, 38]⟩, ⟨GateOp.or, [22, 25]⟩, ⟨GateOp.or, [40, 28]⟩, ⟨GateOp.or, [41, 31]⟩, ⟨GateOp.or, [42, 33]⟩, ⟨GateOp.or, [43, 35]⟩, ⟨GateOp.or, [44, 37]⟩, ⟨GateOp.or, [45, 39]⟩], 46⟩

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

theorem C_size : C.size ≤ 31 := by decide

theorem C_rep : Represents (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19873_aux

theorem PEqualNP.Outside.L_meta_19873 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨PEqualNP.Outside.L_meta_19873_aux.C, PEqualNP.Outside.L_meta_19873_aux.C_mono, PEqualNP.Outside.L_meta_19873_aux.C_size, PEqualNP.Outside.L_meta_19873_aux.C_rep⟩
