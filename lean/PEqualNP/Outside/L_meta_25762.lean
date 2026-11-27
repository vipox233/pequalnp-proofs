import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25762

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def ckt : Circuit :=
  { gates := [
      ⟨GateOp.or, [1, 13]⟩,
      ⟨GateOp.or, [0, 11]⟩,
      ⟨GateOp.or, [4, 9]⟩,
      ⟨GateOp.or, [7, 10]⟩,
      ⟨GateOp.or, [5, 17]⟩,
      ⟨GateOp.or, [2, 17]⟩,
      ⟨GateOp.or, [14, 16]⟩,
      ⟨GateOp.or, [3, 8]⟩,
      ⟨GateOp.or, [5, 15]⟩,
      ⟨GateOp.and, [18, 20]⟩,
      ⟨GateOp.or, [6, 12]⟩,
      ⟨GateOp.or, [16, 24]⟩,
      ⟨GateOp.or, [2, 15]⟩,
      ⟨GateOp.and, [19, 22]⟩,
      ⟨GateOp.or, [21, 24]⟩,
      ⟨GateOp.or, [14, 21]⟩,
      ⟨GateOp.and, [26, 28]⟩,
      ⟨GateOp.and, [25, 29]⟩,
      ⟨GateOp.or, [27, 30]⟩,
      ⟨GateOp.or, [31, 32]⟩,
      ⟨GateOp.or, [23, 33]⟩
    ],
    output := 34 }

def fanB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | GateOp.not => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem fanB_sound (C : Circuit) (h : fanB C = true) : FanInTwo C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem fan : FanInTwo ckt :=
  fanB_sound ckt (by decide +kernel)

theorem rep : Represents (fun (u : Fin 8) (v : Fin 6) => (187576881878421 : ℕ).testBit (6 * u.val + v.val)) ckt := by
  decide +kernel

end PEqualNP.Outside.L_meta_25762

theorem PEqualNP.Outside.L_meta_25762 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 21 ∧ PEqualNP.Represents.Represents (fun (u : Fin 8) (v : Fin 6) => (187576881878421 : ℕ).testBit (6 * u.val + v.val)) C) :=
  ⟨PEqualNP.Outside.L_meta_25762.ckt, PEqualNP.Outside.L_meta_25762.fan, by decide, PEqualNP.Outside.L_meta_25762.rep⟩
