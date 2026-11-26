import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20137_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 8]⟩, ⟨.and, [4, 10]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [16, 9]⟩, ⟨.or, [7, 14]⟩, ⟨.or, [21, 5]⟩, ⟨.or, [9, 22]⟩, ⟨.and, [24, 20]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [5, 24]⟩, ⟨.or, [4, 18]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [29, 20]⟩, ⟨.or, [27, 19]⟩, ⟨.and, [23, 26]⟩, ⟨.and, [28, 30]⟩, ⟨.or, [25, 32]⟩, ⟨.and, [18, 22]⟩, ⟨.or, [35, 34]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [31, 37]⟩, ⟨.or, [36, 33]⟩, ⟨.or, [39, 38]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10998964658842522050 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20137_aux

theorem PEqualNP.Outside.L_meta_20137 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10998964658842522050 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20137_aux.main
