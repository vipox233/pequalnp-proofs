import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20245_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [10, 7]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [11, 20]⟩, ⟨.or, [13, 18]⟩, ⟨.or, [9, 17]⟩, ⟨.or, [19, 5]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [27, 18]⟩, ⟨.or, [27, 26]⟩, ⟨.or, [20, 11]⟩, ⟨.or, [18, 23]⟩, ⟨.and, [31, 25]⟩, ⟨.and, [30, 28]⟩, ⟨.or, [19, 16]⟩, ⟨.or, [22, 34]⟩, ⟨.or, [6, 24]⟩, ⟨.or, [32, 6]⟩, ⟨.and, [37, 29]⟩, ⟨.and, [38, 35]⟩, ⟨.or, [40, 33]⟩, ⟨.or, [41, 36]⟩, ⟨.or, [39, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12886077434404292460 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20245_aux

theorem PEqualNP.Outside.L_meta_20245 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (12886077434404292460 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20245_aux.main
