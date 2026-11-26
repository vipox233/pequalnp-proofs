import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19918_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [9, 12]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.or, [14, 17]⟩, ⟨GateOp.or, [15, 18]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.or, [22, 20]⟩, ⟨GateOp.and, [0, 23]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.and, [1, 25]⟩, ⟨GateOp.or, [17, 21]⟩, ⟨GateOp.and, [2, 27]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [29, 21]⟩, ⟨GateOp.and, [3, 30]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [32, 15]⟩, ⟨GateOp.or, [33, 16]⟩, ⟨GateOp.and, [4, 34]⟩, ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.and, [5, 36]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.and, [6, 38]⟩, ⟨GateOp.or, [10, 15]⟩, ⟨GateOp.or, [40, 19]⟩, ⟨GateOp.and, [7, 41]⟩, ⟨GateOp.or, [24, 26]⟩, ⟨GateOp.or, [43, 28]⟩, ⟨GateOp.or, [44, 31]⟩, ⟨GateOp.or, [45, 35]⟩, ⟨GateOp.or, [46, 37]⟩, ⟨GateOp.or, [47, 39]⟩, ⟨GateOp.or, [48, 42]⟩], 49⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19918_aux

theorem PEqualNP.Outside.L_meta_19918 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14797551480516013530 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨PEqualNP.Outside.L_meta_19918_aux.wit, PEqualNP.Outside.L_meta_19918_aux.wit_mono, by decide, by decide +kernel⟩
