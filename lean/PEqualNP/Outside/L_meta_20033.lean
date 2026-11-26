import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20033_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 11]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [12, 17]⟩, ⟨.or, [16, 10]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [5, 10]⟩, ⟨.or, [8, 6]⟩, ⟨.or, [18, 0]⟩, ⟨.or, [14, 21]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [22, 24]⟩, ⟨.or, [2, 1]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [27, 26]⟩, ⟨.or, [8, 20]⟩, ⟨.or, [16, 1]⟩, ⟨.or, [5, 29]⟩, ⟨.or, [24, 28]⟩, ⟨.or, [13, 23]⟩, ⟨.or, [31, 15]⟩, ⟨.and, [35, 33]⟩, ⟨.or, [15, 25]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [38, 19]⟩, ⟨.and, [32, 34]⟩, ⟨.and, [37, 39]⟩, ⟨.and, [30, 4]⟩, ⟨.or, [36, 40]⟩, ⟨.or, [42, 41]⟩, ⟨.or, [44, 43]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7871934643211302605 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20033_aux

theorem PEqualNP.Outside.L_meta_20033 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7871934643211302605 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20033_aux.main
