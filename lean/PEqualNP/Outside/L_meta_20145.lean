import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20145_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 4]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [13, 1]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [19, 0]⟩, ⟨.and, [15, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [23, 16]⟩, ⟨.or, [22, 21]⟩, ⟨.or, [8, 7]⟩, ⟨.or, [12, 11]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [19, 26]⟩, ⟨.and, [28, 27]⟩, ⟨.or, [29, 3]⟩, ⟨.or, [17, 24]⟩, ⟨.or, [31, 14]⟩, ⟨.or, [18, 24]⟩, ⟨.or, [12, 26]⟩, ⟨.or, [14, 23]⟩, ⟨.and, [34, 33]⟩, ⟨.or, [36, 20]⟩, ⟨.or, [20, 32]⟩, ⟨.or, [25, 18]⟩, ⟨.and, [39, 35]⟩, ⟨.or, [41, 37]⟩, ⟨.and, [40, 38]⟩, ⟨.or, [30, 42]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20145_aux

theorem PEqualNP.Outside.L_meta_20145 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12602045345396281050 : ℕ).testBit (8 * u.val + v.val)) 33 :=
  PEqualNP.Outside.L_meta_20145_aux.main
