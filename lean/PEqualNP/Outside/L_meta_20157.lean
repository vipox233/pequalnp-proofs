import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20157_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [7, 9]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [2, 12]⟩, ⟨.or, [0, 14]⟩, ⟨.or, [20, 6]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [19, 11]⟩, ⟨.or, [10, 1]⟩, ⟨.or, [16, 22]⟩, ⟨.or, [9, 23]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [13, 21]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [22, 29]⟩, ⟨.or, [20, 23]⟩, ⟨.and, [30, 18]⟩, ⟨.or, [13, 3]⟩, ⟨.and, [24, 31]⟩, ⟨.and, [25, 28]⟩, ⟨.and, [26, 33]⟩, ⟨.or, [27, 36]⟩, ⟨.or, [37, 32]⟩, ⟨.or, [38, 34]⟩, ⟨.or, [35, 39]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7531109383139514375 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20157_aux

theorem PEqualNP.Outside.L_meta_20157 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7531109383139514375 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20157_aux.main
