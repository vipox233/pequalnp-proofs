import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20279_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.and, [13, 2]⟩, ⟨.and, [14, 0]⟩, ⟨.or, [16, 0]⟩, ⟨.or, [4, 12]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [23, 21]⟩, ⟨.or, [22, 25]⟩, ⟨.or, [19, 23]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [17, 24]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [30, 27]⟩, ⟨.and, [26, 30]⟩, ⟨.or, [25, 21]⟩, ⟨.and, [35, 28]⟩, ⟨.or, [36, 31]⟩, ⟨.or, [34, 37]⟩, ⟨.and, [32, 33]⟩, ⟨.and, [38, 29]⟩, ⟨.or, [40, 39]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15612158718957067875 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20279_aux

theorem PEqualNP.Outside.L_meta_20279 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15612158718957067875 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20279_aux.main
