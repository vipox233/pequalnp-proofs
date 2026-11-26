import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22293_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [9, 13]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [10, 15]⟩, ⟨.and, [14, 16]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [18, 21]⟩], 22⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837623 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22293_aux

theorem PEqualNP.Outside.L_meta_22293 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (837623 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  exact PEqualNP.Outside.L_meta_22293_aux.main
