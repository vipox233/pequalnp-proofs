import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19881_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 12]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.or, [16, 11]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [22, 13]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [24, 16]⟩, ⟨.or, [6, 8]⟩, ⟨.and, [23, 21]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [26, 4]⟩, ⟨.or, [24, 5]⟩, ⟨.or, [23, 11]⟩, ⟨.or, [14, 29]⟩, ⟨.or, [32, 7]⟩, ⟨.or, [20, 33]⟩, ⟨.or, [22, 34]⟩, ⟨.or, [1, 11]⟩, ⟨.and, [30, 29]⟩, ⟨.and, [29, 36]⟩, ⟨.or, [31, 21]⟩, ⟨.or, [25, 38]⟩, ⟨.or, [37, 28]⟩, ⟨.and, [35, 41]⟩, ⟨.and, [40, 39]⟩, ⟨.or, [42, 43]⟩, ⟨.or, [27, 44]⟩, ⟨.and, [17, 4]⟩, ⟨.or, [46, 45]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176467829879985515 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19881_aux

theorem PEqualNP.Outside.L_meta_19881 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (13176467829879985515 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  PEqualNP.Outside.L_meta_19881_aux.main
