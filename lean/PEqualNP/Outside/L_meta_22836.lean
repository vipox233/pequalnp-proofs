import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22836

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [5, 6]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [10, 11]⟩,
    ⟨GateOp.and, [0, 12]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.or, [11, 14]⟩,
    ⟨GateOp.and, [1, 15]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.or, [6, 7]⟩,
    ⟨GateOp.or, [17, 18]⟩,
    ⟨GateOp.and, [2, 19]⟩,
    ⟨GateOp.and, [3, 17]⟩,
    ⟨GateOp.or, [13, 16]⟩,
    ⟨GateOp.or, [20, 21]⟩,
    ⟨GateOp.or, [22, 23]⟩], output := 24 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851318 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22836

theorem PEqualNP.Outside.L_meta_22836 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851318 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  PEqualNP.Outside.L_meta_22836.main
