import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23055_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [0, 16]⟩, ⟨.and, [17, 19]⟩, ⟨.and, [18, 21]⟩, ⟨.or, [20, 23]⟩, ⟨.or, [22, 24]⟩], 25⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965690 : ℕ).testBit (6 * u.val + v.val)) 16 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23055_aux

theorem PEqualNP.Outside.L_meta_23055 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1965690 : ℕ).testBit (6 * u.val + v.val)) 16) := by
  exact PEqualNP.Outside.L_meta_23055_aux.main
