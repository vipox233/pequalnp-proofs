import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20189_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 0]⟩, ⟨.or, [1, 15]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [14, 4]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [17, 19]⟩, ⟨.or, [10, 7]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [21, 8]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [3, 16]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [25, 28]⟩, ⟨.or, [22, 16]⟩, ⟨.or, [20, 6]⟩, ⟨.and, [20, 28]⟩, ⟨.or, [30, 32]⟩, ⟨.or, [21, 25]⟩, ⟨.and, [23, 29]⟩, ⟨.or, [24, 3]⟩, ⟨.or, [27, 8]⟩, ⟨.and, [34, 37]⟩, ⟨.or, [31, 12]⟩, ⟨.or, [33, 18]⟩, ⟨.and, [40, 39]⟩, ⟨.and, [22, 36]⟩, ⟨.or, [38, 35]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17388182210000334840 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20189_aux

theorem PEqualNP.Outside.L_meta_20189 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17388182210000334840 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20189_aux.main
