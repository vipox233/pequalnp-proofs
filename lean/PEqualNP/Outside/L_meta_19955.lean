import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19955_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 8]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [12, 6]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [1, 22]⟩, ⟨.or, [23, 18]⟩, ⟨.or, [21, 22]⟩, ⟨.or, [0, 17]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [9, 28]⟩, ⟨.or, [29, 17]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [31, 30]⟩, ⟨.and, [32, 19]⟩, ⟨.and, [18, 17]⟩, ⟨.or, [7, 27]⟩, ⟨.and, [31, 27]⟩, ⟨.and, [14, 21]⟩, ⟨.and, [10, 35]⟩, ⟨.or, [4, 20]⟩, ⟨.and, [25, 39]⟩, ⟨.or, [37, 36]⟩, ⟨.and, [24, 15]⟩, ⟨.or, [34, 41]⟩, ⟨.or, [42, 43]⟩, ⟨.or, [44, 33]⟩, ⟨.or, [40, 45]⟩, ⟨.or, [46, 38]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19955_aux

theorem PEqualNP.Outside.L_meta_19955 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10260651070736356020 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19955_aux.main
