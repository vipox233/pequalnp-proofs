import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19819_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [9, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [18, 15]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [21, 15]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [8, 17]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [3, 26]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [28, 14]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [33, 14]⟩, ⟨.and, [6, 34]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [7, 36]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [38, 25]⟩, ⟨.or, [39, 27]⟩, ⟨.or, [40, 30]⟩, ⟨.or, [41, 32]⟩, ⟨.or, [42, 35]⟩, ⟨.or, [43, 37]⟩], 44⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10543322878649664930 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19819_aux

theorem PEqualNP.Outside.L_meta_19819 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10543322878649664930 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_19819_aux.main
