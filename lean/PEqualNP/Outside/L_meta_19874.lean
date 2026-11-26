import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19874_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 3]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [13, 0]⟩, ⟨.or, [18, 17]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [9, 20]⟩, ⟨.and, [16, 19]⟩, ⟨.or, [12, 1]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [8, 4]⟩, ⟨.or, [20, 16]⟩, ⟨.and, [9, 7]⟩, ⟨.or, [24, 23]⟩, ⟨.or, [27, 24]⟩, ⟨.and, [30, 26]⟩, ⟨.or, [22, 28]⟩, ⟨.or, [18, 7]⟩, ⟨.and, [29, 21]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [31, 34]⟩, ⟨.or, [25, 33]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [38, 32]⟩, ⟨.or, [36, 39]⟩], 40⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1892380200682152600 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19874_aux

theorem PEqualNP.Outside.L_meta_19874 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1892380200682152600 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_19874_aux.main
