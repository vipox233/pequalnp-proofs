import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20652

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.and, [2, 5]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.and, [3, 11]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.and, [4, 13]⟩,
    ⟨GateOp.or, [10, 12]⟩,
    ⟨GateOp.or, [14, 15]⟩], output := 16 }

def monoOk : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

theorem mono_of (C : Circuit)
    (h : (C.gates.all fun g => monoOk g.op && decide (g.inputs.length ≤ 2)) = true) :
    PEqualNP.MetaComplexity.Monotone2 C := by
  intro g hg
  have := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  refine ⟨?_, this.2⟩
  have h1 := this.1
  cases hop : g.op <;> simp_all [monoOk]

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6390784 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20652

theorem PEqualNP.Outside.L_meta_20652 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (6390784 : ℕ).testBit (5 * u.val + v.val)) 7 :=
  PEqualNP.Outside.L_meta_20652.main
