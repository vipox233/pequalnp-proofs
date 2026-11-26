import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20170_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 15]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [18, 7]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [6, 3]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [8, 22]⟩, ⟨.or, [23, 16]⟩, ⟨.and, [17, 25]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [23, 3]⟩, ⟨.or, [12, 13]⟩, ⟨.or, [21, 0]⟩, ⟨.or, [24, 15]⟩, ⟨.or, [29, 18]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [1, 27]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [32, 24]⟩, ⟨.and, [33, 28]⟩, ⟨.or, [34, 36]⟩, ⟨.and, [19, 39]⟩, ⟨.or, [31, 27]⟩, ⟨.and, [30, 41]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [38, 43]⟩, ⟨.or, [44, 40]⟩, ⟨.or, [42, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20170_aux

theorem PEqualNP.Outside.L_meta_20170 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17464622044026729945 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20170_aux.main
