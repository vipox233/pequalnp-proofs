import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20026_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 7]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [13, 6]⟩, ⟨.or, [11, 2]⟩, ⟨.or, [15, 1]⟩, ⟨.or, [12, 20]⟩, ⟨.or, [2, 18]⟩, ⟨.or, [5, 22]⟩, ⟨.and, [12, 20]⟩, ⟨.or, [19, 21]⟩, ⟨.and, [21, 5]⟩, ⟨.and, [14, 23]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [30, 20]⟩, ⟨.or, [13, 4]⟩, ⟨.and, [29, 31]⟩, ⟨.and, [32, 25]⟩, ⟨.or, [26, 33]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [27, 35]⟩, ⟨.or, [37, 34]⟩, ⟨.and, [36, 28]⟩, ⟨.or, [38, 39]⟩, ⟨.or, [40, 24]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (813692034574725510 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20026_aux

theorem PEqualNP.Outside.L_meta_20026 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (813692034574725510 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20026_aux.main
