import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21304

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.or, [0, 9]⟩,
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [7, 8]⟩,
    ⟨GateOp.or, [6, 13]⟩,
    ⟨GateOp.and, [4, 10]⟩,
    ⟨GateOp.and, [5, 11]⟩,
    ⟨GateOp.and, [12, 14]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [15, 18]⟩], output := 19 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (102334 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21304

theorem PEqualNP.Outside.L_meta_21304 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (102334 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_21304.main
