import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20096_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 10]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [3, 2]⟩, ⟨.or, [7, 16]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [4, 15]⟩, ⟨.and, [4, 17]⟩, ⟨.or, [12, 0]⟩, ⟨.or, [14, 20]⟩, ⟨.or, [11, 2]⟩, ⟨.and, [24, 18]⟩, ⟨.or, [23, 13]⟩, ⟨.and, [16, 17]⟩, ⟨.or, [11, 4]⟩, ⟨.or, [7, 27]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [8, 31]⟩, ⟨.or, [19, 15]⟩, ⟨.or, [29, 31]⟩, ⟨.or, [28, 26]⟩, ⟨.or, [22, 33]⟩, ⟨.or, [34, 23]⟩, ⟨.or, [36, 5]⟩, ⟨.and, [37, 38]⟩, ⟨.or, [5, 32]⟩, ⟨.or, [35, 39]⟩, ⟨.and, [30, 40]⟩, ⟨.and, [25, 21]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [44, 42]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1970952436485043335 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20096_aux

theorem PEqualNP.Outside.L_meta_20096 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (1970952436485043335 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_20096_aux.main
