import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19744

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := ⟨[⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.or, [21, 17]⟩, ⟨GateOp.and, [0, 22]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.and, [1, 24]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.and, [2, 26]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [28, 19]⟩, ⟨GateOp.and, [3, 29]⟩, ⟨GateOp.or, [9, 15]⟩, ⟨GateOp.or, [31, 17]⟩, ⟨GateOp.and, [4, 32]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [34, 19]⟩, ⟨GateOp.and, [5, 35]⟩, ⟨GateOp.or, [9, 20]⟩, ⟨GateOp.and, [6, 37]⟩, ⟨GateOp.or, [15, 20]⟩, ⟨GateOp.and, [7, 39]⟩, ⟨GateOp.or, [23, 25]⟩, ⟨GateOp.or, [41, 27]⟩, ⟨GateOp.or, [42, 30]⟩, ⟨GateOp.or, [43, 33]⟩, ⟨GateOp.or, [44, 36]⟩, ⟨GateOp.or, [45, 38]⟩, ⟨GateOp.or, [46, 40]⟩], 47⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 8 => (14215526027697465180 : ℕ).testBit (8 * u.val + v.val)) C0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_19744

theorem PEqualNP.Outside.L_meta_19744 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14215526027697465180 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_19744.C0, PEqualNP.Outside.L_meta_19744.mono, by decide, PEqualNP.Outside.L_meta_19744.rep⟩
