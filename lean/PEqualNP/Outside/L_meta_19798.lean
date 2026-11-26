import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19798_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [12, 15]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [19, 15]⟩, ⟨GateOp.and, [0, 20]⟩, ⟨GateOp.or, [12, 16]⟩, ⟨GateOp.and, [1, 22]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [24, 14]⟩, ⟨GateOp.and, [2, 25]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [3, 27]⟩, ⟨GateOp.or, [11, 18]⟩, ⟨GateOp.and, [4, 29]⟩, ⟨GateOp.or, [14, 18]⟩, ⟨GateOp.and, [5, 31]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.and, [6, 33]⟩, ⟨GateOp.or, [8, 17]⟩, ⟨GateOp.and, [7, 35]⟩, ⟨GateOp.or, [21, 23]⟩, ⟨GateOp.or, [37, 26]⟩, ⟨GateOp.or, [38, 28]⟩, ⟨GateOp.or, [39, 30]⟩, ⟨GateOp.or, [40, 32]⟩, ⟨GateOp.or, [41, 34]⟩, ⟨GateOp.or, [42, 36]⟩], 43⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19798_aux

theorem PEqualNP.Outside.L_meta_19798 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (813692034574725510 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨PEqualNP.Outside.L_meta_19798_aux.wit, PEqualNP.Outside.L_meta_19798_aux.wit_mono, by decide, by decide +kernel⟩
