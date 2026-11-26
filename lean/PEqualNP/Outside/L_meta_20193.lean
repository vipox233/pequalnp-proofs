import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20193_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 13]⟩, ⟨.or, [6, 14]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [4, 20]⟩, ⟨.or, [19, 9]⟩, ⟨.or, [4, 17]⟩, ⟨.or, [19, 18]⟩, ⟨.and, [24, 23]⟩, ⟨.or, [18, 21]⟩, ⟨.or, [16, 14]⟩, ⟨.or, [2, 10]⟩, ⟨.and, [16, 26]⟩, ⟨.or, [23, 22]⟩, ⟨.or, [29, 11]⟩, ⟨.or, [5, 31]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [30, 21]⟩, ⟨.or, [27, 24]⟩, ⟨.and, [8, 33]⟩, ⟨.or, [9, 32]⟩, ⟨.and, [37, 35]⟩, ⟨.and, [34, 28]⟩, ⟨.or, [25, 38]⟩, ⟨.or, [39, 40]⟩, ⟨.and, [11, 20]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [43, 42]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20193_aux

theorem PEqualNP.Outside.L_meta_20193 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5662696764710545965 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20193_aux.main
