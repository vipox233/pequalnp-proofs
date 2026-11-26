import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20174_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 8]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [12, 3]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [0, 20]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [18, 5]⟩, ⟨.and, [25, 18]⟩, ⟨.and, [24, 7]⟩, ⟨.or, [21, 14]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [31, 26]⟩, ⟨.or, [32, 20]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [31, 16]⟩, ⟨.or, [27, 25]⟩, ⟨.or, [34, 14]⟩, ⟨.and, [35, 30]⟩, ⟨.and, [33, 22]⟩, ⟨.and, [36, 37]⟩, ⟨.or, [28, 38]⟩, ⟨.or, [39, 41]⟩, ⟨.or, [29, 42]⟩, ⟨.or, [43, 40]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20174_aux

theorem PEqualNP.Outside.L_meta_20174 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20174_aux.main
