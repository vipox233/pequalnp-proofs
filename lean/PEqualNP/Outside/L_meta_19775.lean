import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19775_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circ : Circuit := ⟨[⟨.or, [8, 9]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [19, 15]⟩, ⟨.and, [0, 20]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [1, 22]⟩, ⟨.or, [9, 18]⟩, ⟨.and, [2, 24]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [26, 15]⟩, ⟨.and, [3, 27]⟩, ⟨.or, [15, 16]⟩, ⟨.and, [4, 29]⟩, ⟨.or, [12, 16]⟩, ⟨.and, [5, 31]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [6, 33]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [7, 35]⟩, ⟨.or, [21, 23]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [38, 28]⟩, ⟨.or, [39, 30]⟩, ⟨.or, [40, 32]⟩, ⟨.or, [41, 34]⟩, ⟨.or, [42, 36]⟩], 43⟩

def okB (C : Circuit) : Bool :=
  C.gates.all fun g => (g.op matches GateOp.and || g.op matches GateOp.or) && decide (g.inputs.length ≤ 2)

theorem okB_mono (C : Circuit) (h : okB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp_all

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7508647934801106060 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨circ, okB_mono circ (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19775_aux

theorem PEqualNP.Outside.L_meta_19775 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7508647934801106060 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19775_aux.main
