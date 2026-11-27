import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23057

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [0, 1]⟩,
    ⟨GateOp.or, [2, 3]⟩,
    ⟨GateOp.or, [1, 11]⟩,
    ⟨GateOp.or, [0, 11]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [3, 10]⟩,
    ⟨GateOp.or, [2, 10]⟩,
    ⟨GateOp.and, [4, 12]⟩,
    ⟨GateOp.and, [13, 14]⟩,
    ⟨GateOp.and, [7, 15]⟩,
    ⟨GateOp.and, [8, 16]⟩,
    ⟨GateOp.and, [9, 10]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.or, [17, 22]⟩,
    ⟨GateOp.or, [21, 23]⟩,
    ⟨GateOp.or, [19, 24]⟩], output := 25 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4030078 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23057

theorem PEqualNP.Outside.L_meta_23057 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (4030078 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_23057.main
