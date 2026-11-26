import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21213

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [2, 8]⟩,
    ⟨GateOp.or, [0, 6]⟩,
    ⟨GateOp.and, [10, 11]⟩,
    ⟨GateOp.or, [7, 12]⟩,
    ⟨GateOp.or, [1, 13]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [9, 16]⟩], output := 17 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114427 : ℕ).testBit (5 * u.val + v.val)) 9 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21213

theorem PEqualNP.Outside.L_meta_21213 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (114427 : ℕ).testBit (5 * u.val + v.val)) 9 :=
  PEqualNP.Outside.L_meta_21213.main
