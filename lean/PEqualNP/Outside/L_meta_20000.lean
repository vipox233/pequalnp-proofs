import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20000_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [7, 10]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [13, 4]⟩, ⟨.or, [6, 0]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [7, 6]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [18, 10]⟩, ⟨.or, [9, 21]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [24, 23]⟩, ⟨.and, [8, 25]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [3, 26]⟩, ⟨.and, [27, 28]⟩, ⟨.and, [30, 31]⟩, ⟨.or, [32, 29]⟩, ⟨.and, [20, 18]⟩, ⟨.or, [34, 33]⟩, ⟨.or, [0, 22]⟩, ⟨.or, [24, 15]⟩, ⟨.and, [38, 37]⟩, ⟨.or, [39, 36]⟩, ⟨.or, [40, 35]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5496967495809117315 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20000_aux

theorem PEqualNP.Outside.L_meta_20000 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5496967495809117315 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20000_aux.main
