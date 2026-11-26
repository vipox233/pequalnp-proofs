import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20381_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 4]⟩, ⟨.or, [6, 11]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [15, 10]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [9, 18]⟩, ⟨.or, [19, 9]⟩, ⟨.or, [17, 16]⟩, ⟨.or, [2, 7]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [10, 17]⟩, ⟨.or, [3, 18]⟩, ⟨.and, [30, 23]⟩, ⟨.or, [23, 27]⟩, ⟨.and, [28, 25]⟩, ⟨.or, [31, 29]⟩, ⟨.or, [19, 3]⟩, ⟨.and, [35, 34]⟩, ⟨.or, [33, 36]⟩, ⟨.or, [5, 8]⟩, ⟨.and, [38, 32]⟩, ⟨.or, [37, 39]⟩, ⟨.or, [26, 22]⟩, ⟨.and, [24, 41]⟩, ⟨.or, [42, 40]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20381_aux

theorem PEqualNP.Outside.L_meta_20381 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14245574616248233305 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20381_aux.main
