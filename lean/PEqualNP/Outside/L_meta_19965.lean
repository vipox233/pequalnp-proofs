import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19965_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 3]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [16, 5]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [23, 14]⟩, ⟨.or, [27, 20]⟩, ⟨.and, [28, 24]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [28, 7]⟩, ⟨.or, [4, 25]⟩, ⟨.and, [32, 22]⟩, ⟨.or, [15, 30]⟩, ⟨.and, [18, 15]⟩, ⟨.and, [31, 10]⟩, ⟨.or, [12, 34]⟩, ⟨.or, [0, 37]⟩, ⟨.or, [35, 29]⟩, ⟨.or, [20, 4]⟩, ⟨.or, [36, 33]⟩, ⟨.and, [38, 40]⟩, ⟨.or, [41, 39]⟩, ⟨.and, [19, 26]⟩, ⟨.or, [44, 43]⟩, ⟨.or, [45, 42]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19965_aux

theorem PEqualNP.Outside.L_meta_19965 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19965_aux.main
