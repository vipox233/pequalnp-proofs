import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19870_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [2, 12]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [11, 16]⟩, ⟨.or, [14, 5]⟩, ⟨.or, [2, 10]⟩, ⟨.or, [6, 13]⟩, ⟨.or, [3, 0]⟩, ⟨.and, [23, 18]⟩, ⟨.or, [4, 15]⟩, ⟨.or, [11, 23]⟩, ⟨.or, [8, 25]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [27, 17]⟩, ⟨.or, [0, 16]⟩, ⟨.or, [3, 22]⟩, ⟨.and, [9, 30]⟩, ⟨.or, [28, 7]⟩, ⟨.or, [32, 33]⟩, ⟨.or, [22, 34]⟩, ⟨.or, [21, 26]⟩, ⟨.or, [16, 28]⟩, ⟨.or, [25, 36]⟩, ⟨.or, [31, 8]⟩, ⟨.and, [27, 1]⟩, ⟨.or, [9, 19]⟩, ⟨.and, [35, 38]⟩, ⟨.and, [39, 37]⟩, ⟨.and, [41, 29]⟩, ⟨.or, [44, 43]⟩, ⟨.or, [45, 40]⟩, ⟨.or, [42, 46]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11447215094344424295 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19870_aux

theorem PEqualNP.Outside.L_meta_19870 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (11447215094344424295 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  PEqualNP.Outside.L_meta_19870_aux.main
