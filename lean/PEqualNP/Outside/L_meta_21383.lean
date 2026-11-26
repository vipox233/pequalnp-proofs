import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21383

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [4, 11]⟩, ⟨.or, [11, 8]⟩, ⟨.and, [0, 13]⟩, ⟨.and, [1, 12]⟩, ⟨.and, [9, 10]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [19, 17]⟩], 20⟩

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

theorem main : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105916 : ℕ).testBit (5 * u.val + v.val)) 12) :=
  ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21383

theorem PEqualNP.Outside.L_meta_21383 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (105916 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact PEqualNP.Outside.L_meta_21383.main
