import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19893_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 9]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [6, 20]⟩, ⟨.or, [11, 0]⟩, ⟨.or, [12, 16]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [21, 26]⟩, ⟨.or, [22, 17]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [24, 29]⟩, ⟨.and, [32, 27]⟩, ⟨.and, [23, 14]⟩, ⟨.and, [20, 21]⟩, ⟨.or, [7, 30]⟩, ⟨.or, [34, 33]⟩, ⟨.and, [28, 36]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [39, 35]⟩, ⟨.and, [19, 31]⟩, ⟨.or, [40, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19893_aux

theorem PEqualNP.Outside.L_meta_19893 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5580678593250014130 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_19893_aux.main
