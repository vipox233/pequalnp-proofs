import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20850_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [1, 6]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [5, 11]⟩, ⟨.and, [5, 0]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [14, 12]⟩, ⟨.or, [9, 16]⟩, ⟨.and, [17, 15]⟩, ⟨.or, [10, 18]⟩], 19⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25957441 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20850_aux

theorem PEqualNP.Outside.L_meta_20850 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 5 => (25957441 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_20850_aux.main
