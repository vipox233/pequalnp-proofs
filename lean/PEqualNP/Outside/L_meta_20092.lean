import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20092_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 2]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [3, 14]⟩, ⟨.or, [18, 16]⟩, ⟨.or, [7, 13]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [10, 20]⟩, ⟨.or, [23, 15]⟩, ⟨.or, [19, 15]⟩, ⟨.and, [15, 21]⟩, ⟨.or, [27, 1]⟩, ⟨.or, [26, 22]⟩, ⟨.or, [21, 25]⟩, ⟨.or, [18, 19]⟩, ⟨.or, [30, 4]⟩, ⟨.or, [31, 32]⟩, ⟨.or, [25, 17]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [28, 31]⟩, ⟨.or, [22, 23]⟩, ⟨.or, [10, 4]⟩, ⟨.and, [33, 35]⟩, ⟨.and, [29, 38]⟩, ⟨.and, [37, 36]⟩, ⟨.or, [39, 40]⟩, ⟨.and, [34, 24]⟩, ⟨.or, [41, 43]⟩, ⟨.or, [42, 44]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15374695358257377210 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20092_aux

theorem PEqualNP.Outside.L_meta_20092 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15374695358257377210 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20092_aux.main
