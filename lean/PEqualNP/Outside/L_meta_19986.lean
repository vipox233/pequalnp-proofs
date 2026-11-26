import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19986_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [4, 9]⟩, ⟨.or, [16, 13]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [15, 17]⟩, ⟨.or, [0, 11]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [8, 15]⟩, ⟨.or, [7, 12]⟩, ⟨.or, [13, 22]⟩, ⟨.or, [16, 18]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [7, 5]⟩, ⟨.or, [2, 21]⟩, ⟨.and, [19, 3]⟩, ⟨.and, [6, 24]⟩, ⟨.and, [25, 21]⟩, ⟨.or, [3, 27]⟩, ⟨.or, [12, 26]⟩, ⟨.or, [19, 32]⟩, ⟨.or, [22, 20]⟩, ⟨.or, [28, 17]⟩, ⟨.or, [20, 23]⟩, ⟨.and, [37, 36]⟩, ⟨.or, [31, 29]⟩, ⟨.and, [10, 34]⟩, ⟨.and, [33, 35]⟩, ⟨.or, [40, 38]⟩, ⟨.or, [30, 39]⟩, ⟨.or, [43, 41]⟩, ⟨.or, [44, 42]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7413361890700106610 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19986_aux

theorem PEqualNP.Outside.L_meta_19986 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7413361890700106610 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19986_aux.main
