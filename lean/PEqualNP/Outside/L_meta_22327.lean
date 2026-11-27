import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22327

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [0, 4]⟩,
    ⟨GateOp.or, [3, 8]⟩,
    ⟨GateOp.or, [7, 11]⟩,
    ⟨GateOp.or, [9, 12]⟩,
    ⟨GateOp.and, [10, 13]⟩,
    ⟨GateOp.or, [1, 5]⟩,
    ⟨GateOp.or, [6, 10]⟩,
    ⟨GateOp.or, [11, 16]⟩,
    ⟨GateOp.and, [15, 17]⟩,
    ⟨GateOp.or, [7, 16]⟩,
    ⟨GateOp.and, [2, 19]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.or, [14, 21]⟩], output := 22 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841082 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22327

theorem PEqualNP.Outside.L_meta_22327 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841082 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  PEqualNP.Outside.L_meta_22327.main
