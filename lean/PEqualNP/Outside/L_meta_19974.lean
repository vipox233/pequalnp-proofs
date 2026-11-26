import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19974_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 14]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [15, 8]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [19, 3]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [11, 20]⟩, ⟨.and, [16, 22]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [21, 4]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [8, 24]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [24, 0]⟩, ⟨.and, [31, 32]⟩, ⟨.or, [31, 29]⟩, ⟨.or, [7, 33]⟩, ⟨.or, [35, 15]⟩, ⟨.and, [34, 36]⟩, ⟨.or, [12, 23]⟩, ⟨.and, [38, 30]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [3, 0]⟩, ⟨.and, [26, 41]⟩, ⟨.or, [28, 40]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2183461428884851875 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19974_aux

theorem PEqualNP.Outside.L_meta_19974 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2183461428884851875 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_19974_aux.main
