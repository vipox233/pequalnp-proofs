import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20211_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [5, 15]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [21, 18]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [21, 10]⟩, ⟨.or, [17, 23]⟩, ⟨.or, [29, 20]⟩, ⟨.and, [27, 28]⟩, ⟨.and, [32, 25]⟩, ⟨.or, [26, 18]⟩, ⟨.or, [3, 22]⟩, ⟨.or, [36, 30]⟩, ⟨.and, [30, 19]⟩, ⟨.or, [16, 38]⟩, ⟨.and, [39, 37]⟩, ⟨.and, [31, 35]⟩, ⟨.or, [40, 34]⟩, ⟨.or, [41, 42]⟩, ⟨.or, [33, 43]⟩, ⟨.and, [12, 1]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20211_aux

theorem PEqualNP.Outside.L_meta_20211 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20211_aux.main
