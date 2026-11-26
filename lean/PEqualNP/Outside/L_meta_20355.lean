import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20355_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 3]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [18, 3]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [20, 19]⟩, ⟨.or, [19, 14]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [23, 8]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [25, 22]⟩, ⟨.or, [21, 10]⟩, ⟨.or, [23, 1]⟩, ⟨.or, [28, 27]⟩, ⟨.or, [28, 17]⟩, ⟨.and, [29, 32]⟩, ⟨.or, [24, 26]⟩, ⟨.or, [25, 31]⟩, ⟨.or, [36, 4]⟩, ⟨.and, [35, 33]⟩, ⟨.and, [20, 16]⟩, ⟨.or, [34, 38]⟩, ⟨.or, [37, 39]⟩, ⟨.and, [41, 30]⟩, ⟨.or, [42, 40]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16816131623650294815 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20355_aux

theorem PEqualNP.Outside.L_meta_20355 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16816131623650294815 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20355_aux.main
