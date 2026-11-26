import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22160
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [0, 4]⟩,
  ⟨.or, [3, 6]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [11, 9]⟩,
  ⟨.and, [10, 13]⟩,
  ⟨.or, [8, 12]⟩,
  ⟨.or, [7, 12]⟩,
  ⟨.and, [16, 2]⟩,
  ⟨.or, [1, 5]⟩,
  ⟨.and, [15, 18]⟩,
  ⟨.or, [19, 14]⟩,
  ⟨.or, [17, 20]⟩], 21⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841062 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22160

theorem PEqualNP.Outside.L_meta_22160 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841062 : ℕ).testBit (6 * u.val + v.val)) 12 := PEqualNP.Outside.L_meta_22160.checked
