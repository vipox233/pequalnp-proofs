import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19785_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C : Circuit := ⟨[⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.and, [0, 19]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [21, 14]⟩, ⟨GateOp.and, [1, 22]⟩, ⟨GateOp.or, [15, 18]⟩, ⟨GateOp.and, [2, 24]⟩, ⟨GateOp.or, [8, 17]⟩, ⟨GateOp.and, [3, 26]⟩, ⟨GateOp.or, [9, 18]⟩, ⟨GateOp.and, [4, 28]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [5, 30]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.and, [6, 32]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [34, 15]⟩, ⟨GateOp.and, [7, 35]⟩, ⟨GateOp.or, [20, 23]⟩, ⟨GateOp.or, [37, 25]⟩, ⟨GateOp.or, [38, 27]⟩, ⟨GateOp.or, [39, 29]⟩, ⟨GateOp.or, [40, 31]⟩, ⟨GateOp.or, [41, 33]⟩, ⟨GateOp.or, [42, 36]⟩], 43⟩

theorem C_mono : Monotone2 C := by
  intro g hg
  simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by simp⟩

theorem C_size : C.size ≤ 28 := by decide

theorem C_rep : Represents (fun u v : Fin 8 => (12147342212780283915 : ℕ).testBit (8 * u.val + v.val)) C := by
  decide +kernel

end PEqualNP.Outside.L_meta_19785_aux

theorem PEqualNP.Outside.L_meta_19785 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12147342212780283915 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19785_aux.C, PEqualNP.Outside.L_meta_19785_aux.C_mono, PEqualNP.Outside.L_meta_19785_aux.C_size, PEqualNP.Outside.L_meta_19785_aux.C_rep⟩
