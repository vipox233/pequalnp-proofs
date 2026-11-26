import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21366

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [7, 8]⟩, ⟨.or, [5, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [16, 3]⟩, ⟨.and, [17, 4]⟩, ⟨.or, [12, 15]⟩, ⟨.or, [19, 18]⟩], 20⟩

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

theorem main : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40830 : ℕ).testBit (5 * u.val + v.val)) 12) :=
  ⟨witness, monoTwoB_sound witness (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_21366

theorem PEqualNP.Outside.L_meta_21366 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (40830 : ℕ).testBit (5 * u.val + v.val)) 12) := by
  exact PEqualNP.Outside.L_meta_21366.main
