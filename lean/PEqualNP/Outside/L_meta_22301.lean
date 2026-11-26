import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22301_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [8, 14]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [11, 13]⟩, ⟨.and, [10, 15]⟩, ⟨.and, [0, 17]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [20, 21]⟩], 22⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840629 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22301_aux

theorem PEqualNP.Outside.L_meta_22301 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (840629 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact PEqualNP.Outside.L_meta_22301_aux.main
