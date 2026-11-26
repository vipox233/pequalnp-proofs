import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20061

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [2, 11]⟩, ⟨GateOp.or, [1, 8]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [14, 5]⟩, ⟨GateOp.or, [0, 15]⟩, ⟨GateOp.or, [7, 17]⟩, ⟨GateOp.or, [6, 12]⟩, ⟨GateOp.or, [19, 10]⟩, ⟨GateOp.or, [9, 17]⟩, ⟨GateOp.or, [20, 18]⟩, ⟨GateOp.or, [22, 16]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.and, [4, 10]⟩, ⟨GateOp.or, [4, 3]⟩, ⟨GateOp.or, [24, 21]⟩, ⟨GateOp.or, [19, 24]⟩, ⟨GateOp.or, [28, 21]⟩, ⟨GateOp.and, [23, 32]⟩, ⟨GateOp.or, [12, 20]⟩, ⟨GateOp.or, [31, 3]⟩, ⟨GateOp.and, [26, 35]⟩, ⟨GateOp.and, [27, 34]⟩, ⟨GateOp.and, [16, 36]⟩, ⟨GateOp.or, [34, 30]⟩, ⟨GateOp.or, [23, 16]⟩, ⟨GateOp.and, [40, 25]⟩, ⟨GateOp.or, [13, 37]⟩, ⟨GateOp.or, [29, 42]⟩, ⟨GateOp.and, [43, 39]⟩, ⟨GateOp.or, [41, 36]⟩, ⟨GateOp.and, [44, 34]⟩, ⟨GateOp.or, [33, 44]⟩, ⟨GateOp.or, [45, 47]⟩], 48⟩

theorem wit_mono : Monotone2 wit := by
  intro g hg
  simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17604493529221135470 : ℕ).testBit (8 * u.val + v.val)) 33 := by
  refine ⟨wit, wit_mono, by decide, ?_⟩
  decide

end PEqualNP.Outside.L_meta_20061

theorem PEqualNP.Outside.L_meta_20061 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17604493529221135470 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20061.main_aux
