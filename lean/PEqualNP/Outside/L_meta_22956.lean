import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22956

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [7, 9]⟩,
    ⟨GateOp.or, [5, 10]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.or, [6, 11]⟩,
    ⟨GateOp.or, [4, 8]⟩,
    ⟨GateOp.or, [7, 14]⟩,
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [4, 16]⟩,
    ⟨GateOp.and, [0, 12]⟩,
    ⟨GateOp.and, [1, 13]⟩,
    ⟨GateOp.and, [2, 15]⟩,
    ⟨GateOp.and, [3, 17]⟩,
    ⟨GateOp.or, [19, 21]⟩,
    ⟨GateOp.or, [18, 22]⟩,
    ⟨GateOp.or, [20, 23]⟩], output := 24 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940410 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22956

theorem PEqualNP.Outside.L_meta_22956 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1940410 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  PEqualNP.Outside.L_meta_22956.main
