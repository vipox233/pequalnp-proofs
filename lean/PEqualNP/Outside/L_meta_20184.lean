import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20184_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 15]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [4, 20]⟩, ⟨.or, [7, 17]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [7, 19]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [8, 21]⟩, ⟨.or, [7, 26]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [18, 25]⟩, ⟨.or, [30, 21]⟩, ⟨.or, [2, 16]⟩, ⟨.and, [24, 23]⟩, ⟨.and, [22, 31]⟩, ⟨.or, [6, 33]⟩, ⟨.or, [23, 24]⟩, ⟨.or, [26, 8]⟩, ⟨.or, [2, 18]⟩, ⟨.or, [29, 37]⟩, ⟨.and, [39, 38]⟩, ⟨.and, [27, 28]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [32, 35]⟩, ⟨.or, [34, 42]⟩, ⟨.and, [36, 43]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13346266753825361370 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20184_aux

theorem PEqualNP.Outside.L_meta_20184 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13346266753825361370 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20184_aux.main
