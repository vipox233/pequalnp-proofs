import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20271_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 0]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [2, 16]⟩, ⟨.or, [11, 7]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [24, 5]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [9, 23]⟩, ⟨.or, [23, 26]⟩, ⟨.or, [6, 26]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [18, 20]⟩, ⟨.and, [21, 29]⟩, ⟨.or, [18, 33]⟩, ⟨.and, [32, 27]⟩, ⟨.and, [25, 28]⟩, ⟨.and, [31, 34]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [37, 38]⟩, ⟨.or, [30, 8]⟩, ⟨.or, [31, 40]⟩, ⟨.and, [41, 22]⟩, ⟨.or, [39, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10801013263263746985 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20271_aux

theorem PEqualNP.Outside.L_meta_20271 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10801013263263746985 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20271_aux.main
