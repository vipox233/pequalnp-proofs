import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20043

open PEqualNP.CircuitLowerBounds

def C0 : Circuit := ⟨[⟨GateOp.or, [13, 15]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.or, [9, 17]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [11, 19]⟩, ⟨GateOp.or, [11, 14]⟩, ⟨GateOp.or, [20, 22]⟩, ⟨GateOp.or, [8, 18]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [13, 20]⟩, ⟨GateOp.or, [12, 27]⟩, ⟨GateOp.or, [14, 18]⟩, ⟨GateOp.or, [8, 26]⟩, ⟨GateOp.or, [14, 25]⟩, ⟨GateOp.or, [14, 19]⟩, ⟨GateOp.and, [0, 24]⟩, ⟨GateOp.and, [1, 23]⟩, ⟨GateOp.and, [2, 21]⟩, ⟨GateOp.and, [3, 28]⟩, ⟨GateOp.and, [4, 32]⟩, ⟨GateOp.and, [5, 29]⟩, ⟨GateOp.and, [6, 31]⟩, ⟨GateOp.and, [7, 30]⟩, ⟨GateOp.or, [33, 34]⟩, ⟨GateOp.or, [41, 35]⟩, ⟨GateOp.or, [42, 36]⟩, ⟨GateOp.or, [43, 37]⟩, ⟨GateOp.or, [44, 38]⟩, ⟨GateOp.or, [45, 39]⟩, ⟨GateOp.or, [46, 40]⟩], 47⟩

theorem mono : PEqualNP.MetaComplexity.Monotone2 C0 := by
  intro g hg
  simp only [C0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem rep : PEqualNP.Represents.Represents (fun u v : Fin 8 => (10801013263263746985 : ℕ).testBit (8 * u.val + v.val)) C0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_20043

theorem PEqualNP.Outside.L_meta_20043 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10801013263263746985 : ℕ).testBit (8 * u.val + v.val)) 32 := by
  exact ⟨PEqualNP.Outside.L_meta_20043.C0, PEqualNP.Outside.L_meta_20043.mono, by decide, PEqualNP.Outside.L_meta_20043.rep⟩
