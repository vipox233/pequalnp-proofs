import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22153

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def circuit : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [13, 12]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [15, 10]⟩, ⟨.and, [16, 3]⟩, ⟨.or, [17, 13]⟩, ⟨.or, [18, 12]⟩, ⟨.or, [16, 11]⟩, ⟨.and, [20, 19]⟩], 21⟩

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

end PEqualNP.Outside.L_meta_22153

theorem PEqualNP.Outside.L_meta_22153 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (839163 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  refine ⟨PEqualNP.Outside.L_meta_22153.circuit, PEqualNP.Outside.L_meta_22153.monoTwoB_sound _ (by decide +kernel), by decide, by decide +kernel⟩
