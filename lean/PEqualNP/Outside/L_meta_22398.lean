import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22398

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [15, 16]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [2, 11]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [18, 21]⟩], 22⟩

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

end PEqualNP.Outside.L_meta_22398

theorem PEqualNP.Outside.L_meta_22398 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851773 : ℕ).testBit (6 * u.val + v.val)) 13) := by
  refine ⟨PEqualNP.Outside.L_meta_22398.circuit, PEqualNP.Outside.L_meta_22398.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
