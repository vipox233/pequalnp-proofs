import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22711_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 3]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [13, 2]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [2, 15]⟩, ⟨.and, [16, 8]⟩, ⟨.and, [14, 18]⟩, ⟨.and, [11, 17]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [22, 21]⟩], 23⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908150 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22711_aux

theorem PEqualNP.Outside.L_meta_22711 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (908150 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  exact PEqualNP.Outside.L_meta_22711_aux.main
