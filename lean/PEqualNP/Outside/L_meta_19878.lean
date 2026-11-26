import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19878_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 6]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [1, 19]⟩, ⟨.or, [0, 18]⟩, ⟨.or, [8, 17]⟩, ⟨.or, [23, 3]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [20, 0]⟩, ⟨.or, [6, 27]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [3, 1]⟩, ⟨.or, [14, 31]⟩, ⟨.or, [27, 23]⟩, ⟨.or, [28, 15]⟩, ⟨.or, [26, 32]⟩, ⟨.or, [29, 22]⟩, ⟨.or, [21, 32]⟩, ⟨.and, [25, 24]⟩, ⟨.and, [34, 35]⟩, ⟨.or, [33, 17]⟩, ⟨.or, [38, 15]⟩, ⟨.and, [40, 30]⟩, ⟨.or, [41, 36]⟩, ⟨.and, [37, 43]⟩, ⟨.or, [42, 44]⟩, ⟨.or, [39, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13073558080245330525 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19878_aux

theorem PEqualNP.Outside.L_meta_19878 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13073558080245330525 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19878_aux.main
