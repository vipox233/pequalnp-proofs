import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19990_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [5, 15]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [17, 10]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [18, 17]⟩, ⟨.and, [3, 22]⟩, ⟨.or, [7, 2]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [25, 9]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [23, 27]⟩, ⟨.or, [10, 2]⟩, ⟨.or, [4, 13]⟩, ⟨.or, [24, 19]⟩, ⟨.or, [30, 16]⟩, ⟨.or, [11, 31]⟩, ⟨.or, [33, 31]⟩, ⟨.or, [26, 11]⟩, ⟨.and, [28, 34]⟩, ⟨.and, [35, 32]⟩, ⟨.and, [36, 21]⟩, ⟨.or, [39, 37]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [29, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6099045440807847450 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19990_aux

theorem PEqualNP.Outside.L_meta_19990 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6099045440807847450 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19990_aux.main
