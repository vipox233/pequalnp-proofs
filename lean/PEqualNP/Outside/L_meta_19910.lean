import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19910_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.or, [8, 17]⟩, ⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [21, 12]⟩, ⟨GateOp.or, [22, 13]⟩, ⟨GateOp.or, [23, 15]⟩, ⟨GateOp.and, [0, 24]⟩, ⟨GateOp.or, [17, 19]⟩, ⟨GateOp.and, [1, 26]⟩, ⟨GateOp.or, [18, 20]⟩, ⟨GateOp.and, [2, 28]⟩, ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [30, 19]⟩, ⟨GateOp.and, [3, 31]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.or, [33, 18]⟩, ⟨GateOp.and, [4, 34]⟩, ⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [36, 14]⟩, ⟨GateOp.or, [37, 18]⟩, ⟨GateOp.and, [5, 38]⟩, ⟨GateOp.or, [16, 20]⟩, ⟨GateOp.and, [6, 40]⟩, ⟨GateOp.or, [18, 19]⟩, ⟨GateOp.and, [7, 42]⟩, ⟨GateOp.or, [25, 27]⟩, ⟨GateOp.or, [44, 29]⟩, ⟨GateOp.or, [45, 32]⟩, ⟨GateOp.or, [46, 35]⟩, ⟨GateOp.or, [47, 39]⟩, ⟨GateOp.or, [48, 41]⟩, ⟨GateOp.or, [49, 43]⟩], 50⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19910_aux

theorem PEqualNP.Outside.L_meta_19910 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15737650488314554035 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨PEqualNP.Outside.L_meta_19910_aux.wit, PEqualNP.Outside.L_meta_19910_aux.wit_mono, by decide, by decide +kernel⟩
