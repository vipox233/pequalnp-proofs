import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19823_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [13, 14]⟩, ⟨.or, [13, 15]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [0, 21]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [23, 17]⟩, ⟨.and, [1, 24]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [2, 26]⟩, ⟨.or, [17, 18]⟩, ⟨.and, [3, 28]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [4, 30]⟩, ⟨.or, [10, 15]⟩, ⟨.or, [32, 16]⟩, ⟨.and, [5, 33]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [35, 20]⟩, ⟨.and, [6, 36]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [38, 18]⟩, ⟨.and, [7, 39]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [41, 27]⟩, ⟨.or, [42, 29]⟩, ⟨.or, [43, 31]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 40]⟩], 47⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15612158718957067875 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19823_aux

theorem PEqualNP.Outside.L_meta_19823 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15612158718957067875 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19823_aux.main
