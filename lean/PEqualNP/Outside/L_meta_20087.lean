import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20087_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [13, 2]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [17, 9]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [20, 18]⟩, ⟨.or, [3, 20]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [25, 2]⟩, ⟨.or, [23, 22]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [9, 0]⟩, ⟨.or, [26, 28]⟩, ⟨.or, [0, 24]⟩, ⟨.and, [24, 19]⟩, ⟨.or, [23, 28]⟩, ⟨.and, [30, 10]⟩, ⟨.and, [21, 33]⟩, ⟨.or, [5, 27]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [29, 37]⟩, ⟨.and, [14, 26]⟩, ⟨.and, [38, 36]⟩, ⟨.or, [39, 35]⟩, ⟨.or, [4, 31]⟩, ⟨.and, [11, 42]⟩, ⟨.or, [32, 43]⟩, ⟨.or, [41, 44]⟩, ⟨.or, [34, 40]⟩, ⟨.or, [46, 45]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3718182521909076510 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20087_aux

theorem PEqualNP.Outside.L_meta_20087 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (3718182521909076510 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20087_aux.main
