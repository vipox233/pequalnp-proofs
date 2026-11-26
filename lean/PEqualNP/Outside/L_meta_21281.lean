import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21281_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- An AND/OR circuit found by a search program outside this file; its last gate is the output.
def C_ : Circuit := ⟨[⟨.or, [7, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [10, 5]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [14, 4]⟩, ⟨.and, [13, 15]⟩, ⟨.or, [14, 13]⟩, ⟨.or, [11, 16]⟩, ⟨.and, [18, 17]⟩], 19⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39773 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21281_aux

theorem PEqualNP.Outside.L_meta_21281 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (39773 : ℕ).testBit (5 * u.val + v.val)) 11 :=
  PEqualNP.Outside.L_meta_21281_aux.main
