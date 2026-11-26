import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20345_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 10]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [21, 8]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [1, 18]⟩, ⟨.or, [13, 5]⟩, ⟨.or, [18, 14]⟩, ⟨.or, [15, 26]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [6, 30]⟩, ⟨.or, [27, 20]⟩, ⟨.and, [32, 25]⟩, ⟨.or, [21, 14]⟩, ⟨.or, [34, 4]⟩, ⟨.or, [9, 27]⟩, ⟨.and, [28, 22]⟩, ⟨.or, [36, 16]⟩, ⟨.or, [29, 17]⟩, ⟨.and, [39, 38]⟩, ⟨.or, [11, 31]⟩, ⟨.or, [37, 33]⟩, ⟨.and, [41, 35]⟩, ⟨.or, [40, 43]⟩, ⟨.or, [44, 42]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6627281390824537785 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20345_aux

theorem PEqualNP.Outside.L_meta_20345 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6627281390824537785 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20345_aux.main
