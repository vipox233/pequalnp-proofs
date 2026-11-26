import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19991_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wit : Circuit :=
  ⟨[⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [16, 9]⟩,
    ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [18, 13]⟩,
    ⟨GateOp.or, [10, 14]⟩, ⟨GateOp.or, [11, 15]⟩,
    ⟨GateOp.or, [17, 14]⟩, ⟨GateOp.or, [19, 15]⟩,
    ⟨GateOp.or, [20, 12]⟩, ⟨GateOp.or, [24, 13]⟩,
    ⟨GateOp.or, [19, 10]⟩, ⟨GateOp.or, [20, 21]⟩,
    ⟨GateOp.or, [17, 10]⟩, ⟨GateOp.or, [16, 21]⟩,
    ⟨GateOp.or, [8, 14]⟩, ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [30, 31]⟩,
    ⟨GateOp.and, [0, 22]⟩, ⟨GateOp.and, [1, 23]⟩,
    ⟨GateOp.and, [2, 25]⟩, ⟨GateOp.and, [3, 26]⟩,
    ⟨GateOp.and, [4, 27]⟩, ⟨GateOp.and, [5, 28]⟩,
    ⟨GateOp.and, [6, 29]⟩, ⟨GateOp.and, [7, 32]⟩,
    ⟨GateOp.or, [33, 34]⟩, ⟨GateOp.or, [35, 36]⟩,
    ⟨GateOp.or, [37, 38]⟩, ⟨GateOp.or, [39, 40]⟩,
    ⟨GateOp.or, [41, 42]⟩, ⟨GateOp.or, [43, 44]⟩,
    ⟨GateOp.or, [45, 46]⟩], 47⟩

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

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem main_aux : PEqualNP.Represents.RepSizeAtMost
    (fun u v : Fin 8 => (16256050495690680915 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨wit, monoTwoB_sound wit (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19991_aux

theorem PEqualNP.Outside.L_meta_19991 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16256050495690680915 : ℕ).testBit (8 * u.val + v.val)) 32) :=
  PEqualNP.Outside.L_meta_19991_aux.main_aux
