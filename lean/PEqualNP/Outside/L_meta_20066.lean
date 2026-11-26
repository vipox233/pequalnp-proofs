import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20066_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [14, 1]⟩, ⟨.or, [8, 5]⟩, ⟨.or, [12, 17]⟩, ⟨.and, [8, 1]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [12, 10]⟩, ⟨.or, [3, 11]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [23, 7]⟩, ⟨.or, [9, 4]⟩, ⟨.or, [18, 6]⟩, ⟨.or, [22, 6]⟩, ⟨.or, [18, 20]⟩, ⟨.or, [15, 2]⟩, ⟨.or, [10, 20]⟩, ⟨.and, [26, 13]⟩, ⟨.and, [27, 30]⟩, ⟨.or, [21, 13]⟩, ⟨.or, [31, 32]⟩, ⟨.and, [33, 0]⟩, ⟨.and, [29, 28]⟩, ⟨.or, [34, 19]⟩, ⟨.or, [37, 36]⟩, ⟨.or, [35, 38]⟩, ⟨.and, [25, 24]⟩, ⟨.or, [39, 40]⟩], 41⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20066_aux

theorem PEqualNP.Outside.L_meta_20066 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (9972273704342751540 : ℕ).testBit (8 * u.val + v.val)) 27 :=
  PEqualNP.Outside.L_meta_20066_aux.main
