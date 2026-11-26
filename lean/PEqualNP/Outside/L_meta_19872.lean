import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19872_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 6]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [14, 8]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [7, 4]⟩, ⟨.or, [4, 1]⟩, ⟨.and, [22, 18]⟩, ⟨.or, [19, 7]⟩, ⟨.or, [2, 17]⟩, ⟨.or, [13, 21]⟩, ⟨.or, [25, 16]⟩, ⟨.or, [28, 2]⟩, ⟨.or, [23, 2]⟩, ⟨.and, [28, 17]⟩, ⟨.and, [15, 29]⟩, ⟨.or, [27, 26]⟩, ⟨.and, [13, 30]⟩, ⟨.and, [8, 26]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [36, 14]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [34, 24]⟩, ⟨.or, [31, 39]⟩, ⟨.or, [19, 1]⟩, ⟨.and, [38, 33]⟩, ⟨.or, [40, 35]⟩, ⟨.and, [41, 37]⟩, ⟨.or, [44, 42]⟩, ⟨.or, [32, 45]⟩, ⟨.or, [46, 43]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14523610048827323415 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19872_aux

theorem PEqualNP.Outside.L_meta_19872 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14523610048827323415 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19872_aux.main
