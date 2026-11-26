import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22079

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def wit : Circuit :=
  ⟨[⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [2, 4]⟩, ⟨GateOp.or, [1, 7]⟩, ⟨GateOp.or, [0, 12]⟩,
    ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.or, [3, 6]⟩, ⟨GateOp.and, [0, 9]⟩, ⟨GateOp.and, [14, 15]⟩,
    ⟨GateOp.or, [8, 11]⟩, ⟨GateOp.or, [16, 17]⟩, ⟨GateOp.and, [13, 18]⟩, ⟨GateOp.or, [19, 20]⟩], 21⟩

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

theorem main_aux : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (836977 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_22079

theorem PEqualNP.Outside.L_meta_22079 : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (836977 : ℕ).testBit (6 * u.val + v.val)) 12 :=
  PEqualNP.Outside.L_meta_22079.main_aux
