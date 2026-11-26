import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20175_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 2]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [15, 9]⟩, ⟨.or, [14, 3]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [9, 23]⟩, ⟨.or, [16, 19]⟩, ⟨.and, [25, 22]⟩, ⟨.or, [17, 21]⟩, ⟨.or, [26, 4]⟩, ⟨.or, [28, 13]⟩, ⟨.or, [5, 18]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [29, 31]⟩, ⟨.or, [17, 15]⟩, ⟨.and, [27, 30]⟩, ⟨.and, [24, 1]⟩, ⟨.and, [7, 33]⟩, ⟨.or, [34, 35]⟩, ⟨.or, [32, 36]⟩, ⟨.or, [38, 37]⟩], 39⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20175_aux

theorem PEqualNP.Outside.L_meta_20175 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9901191629971542690 : ℕ).testBit (8 * u.val + v.val)) 24 :=
  PEqualNP.Outside.L_meta_20175_aux.main
