import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19883_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 7]⟩, ⟨.or, [4, 16]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [3, 20]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [19, 13]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [2, 25]⟩, ⟨.or, [27, 24]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [26, 2]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [16, 26]⟩, ⟨.or, [32, 14]⟩, ⟨.or, [23, 30]⟩, ⟨.and, [29, 29]⟩, ⟨.and, [33, 28]⟩, ⟨.or, [12, 23]⟩, ⟨.and, [35, 36]⟩, ⟨.and, [22, 38]⟩, ⟨.or, [39, 37]⟩, ⟨.and, [34, 31]⟩, ⟨.or, [42, 40]⟩, ⟨.and, [21, 18]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17056109459091738360 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19883_aux

theorem PEqualNP.Outside.L_meta_19883 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17056109459091738360 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19883_aux.main
