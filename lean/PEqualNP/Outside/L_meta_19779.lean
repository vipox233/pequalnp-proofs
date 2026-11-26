import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19779_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 11]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.or, [10, 18]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [12, 19]⟩, ⟨.or, [17, 20]⟩, ⟨.and, [0, 23]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [25, 21]⟩, ⟨.and, [1, 26]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [28, 18]⟩, ⟨.and, [2, 29]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [15, 22]⟩, ⟨.and, [4, 33]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [35, 20]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [13, 22]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [18, 21]⟩, ⟨.and, [7, 40]⟩, ⟨.or, [24, 27]⟩, ⟨.or, [42, 30]⟩, ⟨.or, [43, 32]⟩, ⟨.or, [44, 34]⟩, ⟨.or, [45, 37]⟩, ⟨.or, [46, 39]⟩, ⟨.or, [47, 41]⟩], 48⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17455334905265877990 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19779_aux

theorem PEqualNP.Outside.L_meta_19779 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17455334905265877990 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19779_aux.main
