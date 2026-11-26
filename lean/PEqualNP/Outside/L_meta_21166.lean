import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21166
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit := ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [9, 7]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [11, 10]⟩, ⟨GateOp.or, [11, 8]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.or, [10, 3]⟩, ⟨GateOp.and, [13, 15]⟩, ⟨GateOp.or, [14, 16]⟩, ⟨GateOp.and, [12, 17]⟩], 18⟩

def monoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
      Nat.ble g.inputs.length 2

theorem monoB_sound (C : Circuit) (h : monoB C = true) : Monotone2 C := by
  intro g hg
  have hc := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at hc
  refine ⟨?_, hc.2⟩
  cases hop : g.op <;> simp [hop] at hc ⊢

end PEqualNP.Outside.L_meta_21166

theorem PEqualNP.Outside.L_meta_21166 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 5) => (47863 : ℕ).testBit (5 * u.val + v.val)) 10) := by
  exact ⟨PEqualNP.Outside.L_meta_21166.circuit, PEqualNP.Outside.L_meta_21166.monoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
