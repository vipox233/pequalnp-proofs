import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23169_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [11, 14]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [3, 17]⟩, ⟨.and, [15, 18]⟩], 19⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (32378 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23169_aux

theorem PEqualNP.Outside.L_meta_23169 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (32378 : ℕ).testBit (6 * u.val + v.val)) 11) := by
  exact PEqualNP.Outside.L_meta_23169_aux.main
