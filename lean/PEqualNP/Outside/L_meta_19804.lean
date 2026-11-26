import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19804_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 11]⟩, ⟨.or, [3, 7]⟩, ⟨.or, [11, 7]⟩, ⟨.and, [0, 13]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [5, 3]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [19, 20]⟩, ⟨.or, [16, 21]⟩, ⟨.or, [0, 22]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [25, 12]⟩, ⟨.and, [10, 5]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [26, 27]⟩, ⟨.or, [17, 31]⟩, ⟨.and, [29, 33]⟩, ⟨.and, [28, 32]⟩, ⟨.or, [12, 30]⟩, ⟨.or, [2, 36]⟩, ⟨.or, [37, 27]⟩, ⟨.or, [35, 23]⟩, ⟨.and, [24, 38]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [34, 41]⟩], 42⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5928307661352831525 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19804_aux

theorem PEqualNP.Outside.L_meta_19804 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (5928307661352831525 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19804_aux.main
