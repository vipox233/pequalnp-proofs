import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19758_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.or, [10, 15]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [21, 17]⟩, ⟨GateOp.and, [0, 22]⟩, ⟨GateOp.or, [9, 20]⟩, ⟨GateOp.and, [1, 24]⟩, ⟨GateOp.or, [15, 20]⟩, ⟨GateOp.and, [2, 26]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.and, [3, 28]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [30, 18]⟩, ⟨GateOp.and, [4, 31]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.and, [5, 33]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [35, 14]⟩, ⟨GateOp.or, [36, 15]⟩, ⟨GateOp.and, [6, 37]⟩, ⟨GateOp.or, [17, 18]⟩, ⟨GateOp.and, [7, 39]⟩, ⟨GateOp.or, [23, 25]⟩, ⟨GateOp.or, [41, 27]⟩, ⟨GateOp.or, [42, 29]⟩, ⟨GateOp.or, [43, 32]⟩, ⟨GateOp.or, [44, 34]⟩, ⟨GateOp.or, [45, 38]⟩, ⟨GateOp.or, [46, 40]⟩], 47⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19758_aux

theorem PEqualNP.Outside.L_meta_19758 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7413361890700106610 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19758_aux.wit, PEqualNP.Outside.L_meta_19758_aux.wit_mono, by decide, by decide +kernel⟩
