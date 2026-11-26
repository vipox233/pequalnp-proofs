import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20311_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 13]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [9, 8]⟩, ⟨.and, [2, 19]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [9, 15]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [17, 6]⟩, ⟨.or, [15, 25]⟩, ⟨.or, [10, 24]⟩, ⟨.or, [23, 2]⟩, ⟨.or, [4, 12]⟩, ⟨.and, [27, 26]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [28, 6]⟩, ⟨.or, [24, 17]⟩, ⟨.or, [1, 29]⟩, ⟨.or, [16, 34]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [31, 29]⟩, ⟨.and, [37, 22]⟩, ⟨.or, [30, 38]⟩, ⟨.and, [32, 35]⟩, ⟨.and, [36, 33]⟩, ⟨.or, [40, 20]⟩, ⟨.or, [39, 42]⟩, ⟨.or, [43, 41]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10192891319453729625 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20311_aux

theorem PEqualNP.Outside.L_meta_20311 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10192891319453729625 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20311_aux.main
