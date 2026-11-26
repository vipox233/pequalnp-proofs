import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20314_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 6]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [12, 7]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [1, 21]⟩, ⟨.or, [3, 18]⟩, ⟨.or, [14, 25]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [21, 15]⟩, ⟨.or, [3, 9]⟩, ⟨.or, [16, 24]⟩, ⟨.or, [17, 19]⟩, ⟨.and, [30, 29]⟩, ⟨.and, [28, 31]⟩, ⟨.or, [23, 22]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [34, 20]⟩, ⟨.or, [36, 32]⟩, ⟨.and, [27, 35]⟩, ⟨.or, [38, 37]⟩, ⟨.or, [39, 33]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9917578511873611425 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20314_aux

theorem PEqualNP.Outside.L_meta_20314 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9917578511873611425 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  PEqualNP.Outside.L_meta_20314_aux.main
