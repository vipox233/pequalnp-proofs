import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20101_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [10, 6]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [11, 1]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [17, 20]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [24, 10]⟩, ⟨.or, [18, 13]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 15]⟩, ⟨.or, [24, 9]⟩, ⟨.and, [28, 29]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [19, 22]⟩, ⟨.or, [9, 8]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [33, 27]⟩, ⟨.and, [26, 35]⟩, ⟨.or, [6, 25]⟩, ⟨.or, [36, 32]⟩, ⟨.or, [16, 38]⟩, ⟨.and, [37, 23]⟩, ⟨.or, [31, 7]⟩, ⟨.and, [41, 34]⟩, ⟨.or, [42, 39]⟩, ⟨.or, [30, 40]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20101_aux

theorem PEqualNP.Outside.L_meta_20101 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14203909686430943145 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20101_aux.main
