import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21375

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [5, 7]⟩,
    ⟨GateOp.or, [8, 9]⟩,
    ⟨GateOp.or, [6, 9]⟩,
    ⟨GateOp.or, [4, 6]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [0, 10]⟩,
    ⟨GateOp.and, [1, 11]⟩,
    ⟨GateOp.and, [2, 12]⟩,
    ⟨GateOp.and, [3, 13]⟩,
    ⟨GateOp.or, [14, 16]⟩,
    ⟨GateOp.or, [17, 18]⟩,
    ⟨GateOp.or, [15, 19]⟩], output := 20 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103898 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21375

theorem PEqualNP.Outside.L_meta_21375 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (103898 : ℕ).testBit (5 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_21375.main
