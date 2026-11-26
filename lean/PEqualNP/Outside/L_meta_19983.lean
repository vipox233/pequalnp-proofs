import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19983_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 6]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [4, 3]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [15, 16]⟩, ⟨.or, [20, 2]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [22, 13]⟩, ⟨.or, [3, 6]⟩, ⟨.or, [9, 19]⟩, ⟨.or, [4, 21]⟩, ⟨.and, [6, 15]⟩, ⟨.or, [8, 26]⟩, ⟨.or, [23, 20]⟩, ⟨.or, [29, 17]⟩, ⟨.or, [27, 20]⟩, ⟨.or, [9, 11]⟩, ⟨.or, [13, 30]⟩, ⟨.or, [7, 27]⟩, ⟨.and, [31, 34]⟩, ⟨.or, [7, 23]⟩, ⟨.or, [25, 2]⟩, ⟨.or, [18, 2]⟩, ⟨.and, [37, 32]⟩, ⟨.and, [39, 35]⟩, ⟨.and, [33, 38]⟩, ⟨.or, [28, 42]⟩, ⟨.or, [24, 36]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [44, 45]⟩, ⟨.or, [40, 46]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19983_aux

theorem PEqualNP.Outside.L_meta_19983 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14833295300162729415 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19983_aux.main
