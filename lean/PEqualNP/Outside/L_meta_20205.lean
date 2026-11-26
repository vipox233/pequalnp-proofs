import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20205_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [4, 10]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [0, 15]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [6, 23]⟩, ⟨.or, [13, 26]⟩, ⟨.or, [22, 15]⟩, ⟨.or, [14, 29]⟩, ⟨.or, [19, 31]⟩, ⟨.or, [21, 13]⟩, ⟨.or, [23, 1]⟩, ⟨.and, [35, 24]⟩, ⟨.and, [28, 32]⟩, ⟨.or, [12, 25]⟩, ⟨.or, [14, 30]⟩, ⟨.or, [38, 6]⟩, ⟨.and, [39, 40]⟩, ⟨.or, [37, 41]⟩, ⟨.and, [34, 33]⟩, ⟨.or, [36, 43]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20205_aux

theorem PEqualNP.Outside.L_meta_20205 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17069659891248394590 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20205_aux.main
