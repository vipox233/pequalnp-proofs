import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19755_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 15]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [22, 19]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [27, 18]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [3, 30]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [4, 32]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [34, 14]⟩, ⟨.or, [35, 17]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [38, 15]⟩, ⟨.or, [39, 18]⟩, ⟨.and, [6, 40]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [7, 42]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [44, 29]⟩, ⟨.or, [45, 31]⟩, ⟨.or, [46, 33]⟩, ⟨.or, [47, 37]⟩, ⟨.or, [48, 41]⟩, ⟨.or, [49, 43]⟩], 50⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19755_aux

theorem PEqualNP.Outside.L_meta_19755 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  PEqualNP.Outside.L_meta_19755_aux.main
