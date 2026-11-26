import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21221

open PEqualNP.CircuitLowerBounds

def c1 : Circuit := { gates := [
    ⟨GateOp.or, [0, 5]⟩,
    ⟨GateOp.or, [1, 9]⟩,
    ⟨GateOp.or, [3, 7]⟩,
    ⟨GateOp.or, [8, 11]⟩,
    ⟨GateOp.and, [10, 12]⟩,
    ⟨GateOp.or, [4, 13]⟩,
    ⟨GateOp.or, [11, 10]⟩,
    ⟨GateOp.or, [2, 6]⟩,
    ⟨GateOp.and, [15, 16]⟩,
    ⟨GateOp.or, [14, 17]⟩], output := 18 }

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241597 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨c1, mono_of c1 (by decide +kernel), by decide +kernel, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21221

theorem PEqualNP.Outside.L_meta_21221 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (241597 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21221.main
