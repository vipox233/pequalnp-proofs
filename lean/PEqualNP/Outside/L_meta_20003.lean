import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20003_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 4]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [5, 4]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 11]⟩, ⟨.and, [1, 14]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [20, 16]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [5, 22]⟩, ⟨.or, [20, 25]⟩, ⟨.and, [22, 25]⟩, ⟨.or, [21, 12]⟩, ⟨.or, [0, 24]⟩, ⟨.or, [26, 2]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [30, 27]⟩, ⟨.and, [19, 28]⟩, ⟨.or, [23, 7]⟩, ⟨.and, [34, 37]⟩, ⟨.or, [36, 35]⟩, ⟨.or, [33, 39]⟩, ⟨.or, [29, 40]⟩, ⟨.or, [41, 38]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7508647934801106060 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20003_aux

theorem PEqualNP.Outside.L_meta_20003 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7508647934801106060 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20003_aux.main
