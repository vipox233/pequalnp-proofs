import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21197_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 6]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [8, 11]⟩, ⟨.or, [11, 9]⟩, ⟨.and, [13, 10]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [16, 17]⟩], 18⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105913 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21197_aux

theorem PEqualNP.Outside.L_meta_21197 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105913 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21197_aux.main
