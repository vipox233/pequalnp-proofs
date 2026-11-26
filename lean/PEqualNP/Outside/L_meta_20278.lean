import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20278_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 10]⟩, ⟨.or, [1, 11]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [12, 6]⟩, ⟨.and, [7, 19]⟩, ⟨.or, [13, 22]⟩, ⟨.or, [4, 24]⟩, ⟨.or, [3, 15]⟩, ⟨.or, [21, 17]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [28, 4]⟩, ⟨.or, [7, 21]⟩, ⟨.or, [26, 16]⟩, ⟨.or, [31, 22]⟩, ⟨.and, [27, 20]⟩, ⟨.and, [30, 29]⟩, ⟨.or, [26, 14]⟩, ⟨.and, [25, 35]⟩, ⟨.or, [36, 34]⟩, ⟨.and, [32, 18]⟩, ⟨.or, [38, 33]⟩, ⟨.or, [39, 37]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6395723629099427220 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20278_aux

theorem PEqualNP.Outside.L_meta_20278 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6395723629099427220 : ℕ).testBit (8 * u.val + v.val)) 25 :=
  PEqualNP.Outside.L_meta_20278_aux.main
