import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19934_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 9]⟩, ⟨GateOp.or, [12, 14]⟩, ⟨GateOp.or, [10, 16]⟩, ⟨GateOp.and, [0, 18]⟩, ⟨GateOp.or, [10, 12]⟩, ⟨GateOp.or, [20, 13]⟩, ⟨GateOp.and, [1, 21]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [23, 15]⟩, ⟨GateOp.and, [2, 24]⟩, ⟨GateOp.or, [15, 16]⟩, ⟨GateOp.and, [3, 26]⟩, ⟨GateOp.or, [8, 13]⟩, ⟨GateOp.or, [28, 14]⟩, ⟨GateOp.and, [4, 29]⟩, ⟨GateOp.or, [15, 17]⟩, ⟨GateOp.and, [5, 31]⟩, ⟨GateOp.or, [11, 17]⟩, ⟨GateOp.and, [6, 33]⟩, ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [35, 13]⟩, ⟨GateOp.and, [7, 36]⟩, ⟨GateOp.or, [19, 22]⟩, ⟨GateOp.or, [38, 25]⟩, ⟨GateOp.or, [39, 27]⟩, ⟨GateOp.or, [40, 30]⟩, ⟨GateOp.or, [41, 32]⟩, ⟨GateOp.or, [42, 34]⟩, ⟨GateOp.or, [43, 37]⟩], 44⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

end PEqualNP.Outside.L_meta_19934_aux

theorem PEqualNP.Outside.L_meta_19934 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3051417864780919815 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨PEqualNP.Outside.L_meta_19934_aux.wit, PEqualNP.Outside.L_meta_19934_aux.wit_mono, by decide, by decide +kernel⟩
