import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20353_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [12, 6]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [17, 2]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [7, 15]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [23, 25]⟩, ⟨.or, [26, 4]⟩, ⟨.or, [20, 26]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [28, 14]⟩, ⟨.and, [31, 22]⟩, ⟨.and, [30, 18]⟩, ⟨.or, [21, 24]⟩, ⟨.or, [19, 32]⟩, ⟨.and, [35, 29]⟩, ⟨.and, [27, 34]⟩, ⟨.or, [37, 33]⟩, ⟨.or, [36, 38]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7226616402994737825 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20353_aux

theorem PEqualNP.Outside.L_meta_20353 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7226616402994737825 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  PEqualNP.Outside.L_meta_20353_aux.main
