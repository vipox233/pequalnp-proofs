import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20030_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 6]⟩, ⟨.or, [16, 3]⟩, ⟨.or, [9, 1]⟩, ⟨.or, [10, 3]⟩, ⟨.or, [2, 12]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [15, 7]⟩, ⟨.or, [20, 0]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [24, 11]⟩, ⟨.or, [20, 10]⟩, ⟨.or, [17, 25]⟩, ⟨.and, [23, 27]⟩, ⟨.and, [17, 11]⟩, ⟨.or, [24, 18]⟩, ⟨.or, [13, 19]⟩, ⟨.or, [30, 26]⟩, ⟨.or, [31, 10]⟩, ⟨.or, [33, 16]⟩, ⟨.or, [34, 18]⟩, ⟨.and, [31, 30]⟩, ⟨.or, [6, 32]⟩, ⟨.and, [35, 4]⟩, ⟨.or, [38, 28]⟩, ⟨.and, [13, 0]⟩, ⟨.and, [37, 22]⟩, ⟨.or, [29, 36]⟩, ⟨.or, [39, 21]⟩, ⟨.or, [43, 41]⟩, ⟨.or, [42, 44]⟩, ⟨.or, [40, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1700870159931663465 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20030_aux

theorem PEqualNP.Outside.L_meta_20030 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1700870159931663465 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_20030_aux.main
