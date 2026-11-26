import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19946_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 4]⟩, ⟨.or, [7, 1]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [20, 12]⟩, ⟨.or, [20, 13]⟩, ⟨.or, [9, 16]⟩, ⟨.or, [22, 8]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [21, 27]⟩, ⟨.or, [1, 25]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [28, 19]⟩, ⟨.or, [32, 23]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [29, 12]⟩, ⟨.and, [24, 17]⟩, ⟨.or, [18, 5]⟩, ⟨.and, [30, 36]⟩, ⟨.and, [38, 35]⟩, ⟨.or, [33, 3]⟩, ⟨.or, [40, 39]⟩, ⟨.or, [34, 26]⟩, ⟨.or, [37, 42]⟩, ⟨.and, [41, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19946_aux

theorem PEqualNP.Outside.L_meta_19946 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7482418488621907005 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_19946_aux.main
