import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22852_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [10, 16]⟩, ⟨.and, [10, 17]⟩, ⟨.and, [2, 18]⟩, ⟨.and, [11, 19]⟩, ⟨.or, [20, 22]⟩, ⟨.or, [21, 23]⟩], 24⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908158 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22852_aux

theorem PEqualNP.Outside.L_meta_22852 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908158 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  exact PEqualNP.Outside.L_meta_22852_aux.main
