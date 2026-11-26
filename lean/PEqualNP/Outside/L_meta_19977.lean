import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19977_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 14]⟩, ⟨.or, [11, 13]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [13, 16]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [15, 0]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [24, 27]⟩, ⟨.or, [25, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [13, 23]⟩, ⟨.or, [20, 24]⟩, ⟨.and, [29, 22]⟩, ⟨.or, [27, 31]⟩, ⟨.or, [26, 29]⟩, ⟨.or, [20, 35]⟩, ⟨.and, [17, 4]⟩, ⟨.and, [26, 28]⟩, ⟨.or, [32, 37]⟩, ⟨.and, [34, 39]⟩, ⟨.or, [38, 40]⟩, ⟨.and, [36, 30]⟩, ⟨.and, [9, 31]⟩, ⟨.or, [33, 41]⟩, ⟨.or, [42, 44]⟩, ⟨.or, [45, 43]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19977_aux

theorem PEqualNP.Outside.L_meta_19977 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19977_aux.main
