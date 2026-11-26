import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22376
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [5, 8]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.or, [6, 11]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [3, 13]⟩,
  ⟨.or, [1, 2]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.and, [0, 9]⟩,
  ⟨.and, [12, 15]⟩,
  ⟨.and, [10, 16]⟩,
  ⟨.or, [18, 19]⟩,
  ⟨.or, [17, 20]⟩,
  ⟨.or, [14, 21]⟩], 22⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841714 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22376

theorem PEqualNP.Outside.L_meta_22376 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841714 : ℕ).testBit (6 * u.val + v.val)) 13 := @PEqualNP.Outside.L_meta_22376.checked
