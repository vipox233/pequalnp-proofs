import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19751_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 12]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [10, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [17, 21]⟩, ⟨.and, [0, 22]⟩, ⟨.or, [14, 17]⟩, ⟨.or, [24, 19]⟩, ⟨.and, [1, 25]⟩, ⟨.or, [12, 18]⟩, ⟨.or, [27, 19]⟩, ⟨.and, [2, 28]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [30, 19]⟩, ⟨.and, [3, 31]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [33, 18]⟩, ⟨.and, [4, 34]⟩, ⟨.or, [16, 20]⟩, ⟨.and, [5, 36]⟩, ⟨.or, [16, 21]⟩, ⟨.and, [6, 38]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [40, 20]⟩, ⟨.and, [7, 41]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [43, 29]⟩, ⟨.or, [44, 32]⟩, ⟨.or, [45, 35]⟩, ⟨.or, [46, 37]⟩, ⟨.or, [47, 39]⟩, ⟨.or, [48, 42]⟩], 49⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19751_aux

theorem PEqualNP.Outside.L_meta_19751 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10337339320775273190 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19751_aux.main
