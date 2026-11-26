import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19875_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 11]⟩, ⟨.or, [13, 11]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [9, 15]⟩, ⟨.and, [6, 17]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [20, 12]⟩, ⟨.or, [1, 4]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [18, 23]⟩, ⟨.or, [9, 21]⟩, ⟨.or, [23, 19]⟩, ⟨.and, [26, 24]⟩, ⟨.or, [27, 8]⟩, ⟨.or, [27, 4]⟩, ⟨.or, [22, 5]⟩, ⟨.or, [30, 19]⟩, ⟨.and, [28, 25]⟩, ⟨.or, [0, 33]⟩, ⟨.and, [31, 38]⟩, ⟨.and, [34, 35]⟩, ⟨.and, [36, 29]⟩, ⟨.and, [39, 39]⟩, ⟨.or, [42, 40]⟩, ⟨.or, [32, 43]⟩, ⟨.or, [37, 41]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5146091177712921810 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19875_aux

theorem PEqualNP.Outside.L_meta_19875 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5146091177712921810 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_19875_aux.main
