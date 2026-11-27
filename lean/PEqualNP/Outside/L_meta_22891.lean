import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22891_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 5]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [13, 17]⟩, ⟨.and, [16, 17]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [4, 20]⟩, ⟨.and, [18, 22]⟩, ⟨.or, [21, 23]⟩], 24⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939370 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22891_aux

theorem PEqualNP.Outside.L_meta_22891 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1939370 : ℕ).testBit (6 * u.val + v.val)) 15) := by
  exact PEqualNP.Outside.L_meta_22891_aux.main
