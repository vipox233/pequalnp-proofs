import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19766_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [11, 13]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [14, 18]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.or, [18, 21]⟩, ⟨GateOp.and, [0, 23]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [25, 12]⟩, ⟨GateOp.or, [26, 19]⟩, ⟨GateOp.and, [1, 27]⟩, ⟨GateOp.or, [17, 20]⟩, ⟨GateOp.and, [2, 29]⟩, ⟨GateOp.or, [9, 22]⟩, ⟨GateOp.and, [3, 31]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [33, 21]⟩, ⟨GateOp.and, [4, 34]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.or, [36, 17]⟩, ⟨GateOp.and, [5, 37]⟩, ⟨GateOp.or, [16, 20]⟩, ⟨GateOp.and, [6, 39]⟩, ⟨GateOp.or, [10, 22]⟩, ⟨GateOp.and, [7, 41]⟩, ⟨GateOp.or, [24, 28]⟩, ⟨GateOp.or, [43, 30]⟩, ⟨GateOp.or, [44, 32]⟩, ⟨GateOp.or, [45, 35]⟩, ⟨GateOp.or, [46, 38]⟩, ⟨GateOp.or, [47, 40]⟩, ⟨GateOp.or, [48, 42]⟩], 49⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19766_aux

theorem PEqualNP.Outside.L_meta_19766 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17030148307327572375 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19766_aux.wit, PEqualNP.Outside.L_meta_19766_aux.wit_mono, by decide, by decide +kernel⟩
