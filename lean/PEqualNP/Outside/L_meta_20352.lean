import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20352_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 0]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [8, 18]⟩, ⟨.or, [3, 19]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [17, 15]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [18, 19]⟩, ⟨.and, [9, 6]⟩, ⟨.or, [25, 3]⟩, ⟨.or, [21, 13]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [13, 24]⟩, ⟨.or, [24, 22]⟩, ⟨.or, [9, 6]⟩, ⟨.and, [23, 28]⟩, ⟨.or, [28, 27]⟩, ⟨.or, [31, 25]⟩, ⟨.and, [32, 29]⟩, ⟨.or, [26, 22]⟩, ⟨.and, [36, 38]⟩, ⟨.or, [30, 35]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [34, 41]⟩, ⟨.and, [33, 40]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20352_aux

theorem PEqualNP.Outside.L_meta_20352 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13373287136702659755 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20352_aux.main
