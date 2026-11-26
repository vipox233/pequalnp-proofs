import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19914_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 10]⟩, ⟨GateOp.or, [9, 13]⟩, ⟨GateOp.or, [11, 15]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.and, [0, 20]⟩, ⟨GateOp.or, [11, 12]⟩, ⟨GateOp.or, [22, 17]⟩, ⟨GateOp.and, [1, 23]⟩, ⟨GateOp.or, [14, 15]⟩, ⟨GateOp.or, [25, 17]⟩, ⟨GateOp.and, [2, 26]⟩, ⟨GateOp.or, [9, 14]⟩, ⟨GateOp.or, [28, 18]⟩, ⟨GateOp.and, [3, 29]⟩, ⟨GateOp.or, [16, 19]⟩, ⟨GateOp.and, [4, 31]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [33, 18]⟩, ⟨GateOp.and, [5, 34]⟩, ⟨GateOp.or, [16, 18]⟩, ⟨GateOp.and, [6, 36]⟩, ⟨GateOp.or, [10, 13]⟩, ⟨GateOp.or, [38, 19]⟩, ⟨GateOp.and, [7, 39]⟩, ⟨GateOp.or, [21, 24]⟩, ⟨GateOp.or, [41, 27]⟩, ⟨GateOp.or, [42, 30]⟩, ⟨GateOp.or, [43, 32]⟩, ⟨GateOp.or, [44, 35]⟩, ⟨GateOp.or, [45, 37]⟩, ⟨GateOp.or, [46, 40]⟩], 47⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19914_aux

theorem PEqualNP.Outside.L_meta_19914 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8398537473870936615 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨PEqualNP.Outside.L_meta_19914_aux.wit, PEqualNP.Outside.L_meta_19914_aux.wit_mono, by decide, by decide +kernel⟩
