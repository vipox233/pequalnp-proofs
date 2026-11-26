import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19958_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [13, 6]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [15, 3]⟩, ⟨.or, [1, 8]⟩, ⟨.or, [5, 19]⟩, ⟨.or, [14, 7]⟩, ⟨.and, [14, 20]⟩, ⟨.or, [21, 11]⟩, ⟨.and, [17, 23]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [20, 18]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [16, 26]⟩, ⟨.or, [25, 27]⟩, ⟨.or, [19, 22]⟩, ⟨.or, [0, 8]⟩, ⟨.and, [16, 29]⟩, ⟨.or, [24, 5]⟩, ⟨.or, [28, 9]⟩, ⟨.or, [21, 34]⟩, ⟨.or, [33, 29]⟩, ⟨.or, [32, 30]⟩, ⟨.or, [18, 37]⟩, ⟨.or, [11, 17]⟩, ⟨.or, [12, 38]⟩, ⟨.and, [36, 39]⟩, ⟨.and, [40, 35]⟩, ⟨.and, [25, 31]⟩, ⟨.or, [42, 43]⟩, ⟨.or, [41, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19958_aux

theorem PEqualNP.Outside.L_meta_19958 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10778182828540224060 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19958_aux.main
