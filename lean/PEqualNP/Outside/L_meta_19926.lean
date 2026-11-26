import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19926_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [12, 13]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [15, 19]⟩, ⟨GateOp.or, [9, 10]⟩, ⟨GateOp.or, [22, 15]⟩, ⟨GateOp.or, [23, 18]⟩, ⟨GateOp.and, [0, 24]⟩, ⟨GateOp.or, [11, 16]⟩, ⟨GateOp.or, [26, 18]⟩, ⟨GateOp.and, [1, 27]⟩, ⟨GateOp.or, [12, 21]⟩, ⟨GateOp.and, [2, 29]⟩, ⟨GateOp.or, [13, 14]⟩, ⟨GateOp.or, [31, 20]⟩, ⟨GateOp.and, [3, 32]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.and, [4, 34]⟩, ⟨GateOp.or, [8, 21]⟩, ⟨GateOp.and, [5, 36]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.and, [6, 38]⟩, ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.and, [7, 40]⟩, ⟨GateOp.or, [25, 28]⟩, ⟨GateOp.or, [42, 30]⟩, ⟨GateOp.or, [43, 33]⟩, ⟨GateOp.or, [44, 35]⟩, ⟨GateOp.or, [45, 37]⟩, ⟨GateOp.or, [46, 39]⟩, ⟨GateOp.or, [47, 41]⟩], 48⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19926_aux

theorem PEqualNP.Outside.L_meta_19926 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13064884772727831990 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨PEqualNP.Outside.L_meta_19926_aux.wit, PEqualNP.Outside.L_meta_19926_aux.wit_mono, by decide, by decide +kernel⟩
