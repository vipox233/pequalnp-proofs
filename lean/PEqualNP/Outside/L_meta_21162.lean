import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21162_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- An AND/OR circuit found by a search program outside this file; its last gate is the output.
def C_ : Circuit := ⟨[⟨.or, [1, 6]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [3, 12]⟩, ⟨.or, [4, 14]⟩, ⟨.or, [15, 10]⟩, ⟨.and, [16, 17]⟩], 18⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40766 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21162_aux

theorem PEqualNP.Outside.L_meta_21162 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40766 : ℕ).testBit (5 * u.val + v.val)) 10 :=
  PEqualNP.Outside.L_meta_21162_aux.main
