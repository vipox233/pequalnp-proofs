import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20372_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [1, 19]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [20, 21]⟩, ⟨.and, [22, 12]⟩, ⟨.or, [23, 11]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [26, 24]⟩, ⟨.or, [25, 16]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [19, 21]⟩, ⟨.or, [29, 27]⟩, ⟨.or, [30, 0]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [30, 27]⟩, ⟨.and, [32, 31]⟩, ⟨.and, [33, 25]⟩, ⟨.or, [22, 12]⟩, ⟨.and, [28, 38]⟩, ⟨.and, [35, 34]⟩, ⟨.or, [37, 40]⟩, ⟨.or, [36, 41]⟩, ⟨.or, [42, 39]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20372_aux

theorem PEqualNP.Outside.L_meta_20372 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11914988824647881820 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20372_aux.main
