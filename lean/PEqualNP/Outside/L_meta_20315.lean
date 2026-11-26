import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20315_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 3]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [6, 12]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [4, 9]⟩, ⟨.and, [14, 1]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [24, 22]⟩, ⟨.and, [23, 17]⟩, ⟨.or, [27, 23]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [29, 21]⟩, ⟨.and, [31, 18]⟩, ⟨.or, [20, 24]⟩, ⟨.or, [19, 30]⟩, ⟨.or, [27, 19]⟩, ⟨.and, [35, 21]⟩, ⟨.or, [36, 26]⟩, ⟨.or, [28, 34]⟩, ⟨.and, [38, 33]⟩, ⟨.or, [37, 25]⟩, ⟨.or, [32, 39]⟩, ⟨.or, [41, 40]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3718182521909076510 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20315_aux

theorem PEqualNP.Outside.L_meta_20315 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3718182521909076510 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20315_aux.main
