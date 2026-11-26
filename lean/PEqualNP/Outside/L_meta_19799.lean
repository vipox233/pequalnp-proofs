import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19799_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 6]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [9, 0]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [17, 5]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [20, 18]⟩, ⟨.and, [14, 3]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [21, 9]⟩, ⟨.or, [3, 17]⟩, ⟨.or, [24, 7]⟩, ⟨.or, [22, 11]⟩, ⟨.or, [14, 25]⟩, ⟨.or, [16, 27]⟩, ⟨.or, [26, 25]⟩, ⟨.and, [29, 31]⟩, ⟨.or, [3, 30]⟩, ⟨.or, [20, 12]⟩, ⟨.or, [16, 35]⟩, ⟨.or, [23, 28]⟩, ⟨.and, [32, 36]⟩, ⟨.and, [28, 19]⟩, ⟨.or, [33, 38]⟩, ⟨.or, [34, 39]⟩, ⟨.and, [41, 37]⟩, ⟨.or, [40, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8660023402198307685 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19799_aux

theorem PEqualNP.Outside.L_meta_19799 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (8660023402198307685 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19799_aux.main
