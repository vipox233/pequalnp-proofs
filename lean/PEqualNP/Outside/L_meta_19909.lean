import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19909_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 14]⟩, ⟨.or, [5, 13]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [12, 2]⟩, ⟨.or, [19, 5]⟩, ⟨.and, [13, 20]⟩, ⟨.or, [21, 11]⟩, ⟨.or, [15, 5]⟩, ⟨.or, [22, 6]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [23, 12]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [25, 16]⟩, ⟨.or, [4, 26]⟩, ⟨.and, [30, 27]⟩, ⟨.or, [19, 28]⟩, ⟨.or, [28, 9]⟩, ⟨.or, [17, 18]⟩, ⟨.or, [34, 27]⟩, ⟨.and, [29, 32]⟩, ⟨.and, [33, 18]⟩, ⟨.or, [37, 36]⟩, ⟨.and, [1, 14]⟩, ⟨.and, [24, 35]⟩, ⟨.or, [31, 39]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10998964658842522050 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19909_aux

theorem PEqualNP.Outside.L_meta_19909 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10998964658842522050 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19909_aux.main
