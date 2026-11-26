import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20362_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [0, 14]⟩, ⟨.or, [1, 13]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [12, 5]⟩, ⟨.or, [11, 18]⟩, ⟨.and, [14, 0]⟩, ⟨.and, [20, 19]⟩, ⟨.or, [23, 17]⟩, ⟨.and, [6, 11]⟩, ⟨.or, [16, 20]⟩, ⟨.or, [19, 26]⟩, ⟨.or, [24, 21]⟩, ⟨.or, [18, 27]⟩, ⟨.and, [30, 25]⟩, ⟨.or, [6, 22]⟩, ⟨.or, [4, 9]⟩, ⟨.or, [27, 33]⟩, ⟨.and, [29, 34]⟩, ⟨.or, [33, 28]⟩, ⟨.and, [36, 32]⟩, ⟨.or, [35, 37]⟩, ⟨.or, [31, 38]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (975669345196721520 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20362_aux

theorem PEqualNP.Outside.L_meta_20362 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (975669345196721520 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20362_aux.main
