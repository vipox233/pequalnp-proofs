import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19972_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 7]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [2, 18]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [11, 14]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [10, 17]⟩, ⟨.and, [22, 3]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [19, 30]⟩, ⟨.or, [10, 24]⟩, ⟨.and, [34, 17]⟩, ⟨.and, [27, 31]⟩, ⟨.or, [28, 9]⟩, ⟨.or, [27, 34]⟩, ⟨.or, [32, 29]⟩, ⟨.or, [33, 35]⟩, ⟨.or, [36, 26]⟩, ⟨.and, [39, 37]⟩, ⟨.or, [40, 41]⟩, ⟨.or, [42, 43]⟩, ⟨.and, [38, 21]⟩, ⟨.or, [44, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14215526027697465180 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19972_aux

theorem PEqualNP.Outside.L_meta_19972 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14215526027697465180 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19972_aux.main
