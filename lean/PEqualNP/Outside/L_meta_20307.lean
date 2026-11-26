import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20307_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 0]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [8, 16]⟩, ⟨.or, [3, 13]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [1, 14]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [17, 22]⟩, ⟨.or, [7, 17]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [26, 23]⟩, ⟨.or, [10, 25]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [19, 10]⟩, ⟨.or, [0, 31]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [24, 20]⟩, ⟨.or, [8, 27]⟩, ⟨.or, [35, 29]⟩, ⟨.or, [28, 21]⟩, ⟨.or, [30, 27]⟩, ⟨.and, [32, 36]⟩, ⟨.and, [33, 37]⟩, ⟨.or, [39, 40]⟩, ⟨.or, [38, 15]⟩, ⟨.and, [42, 34]⟩, ⟨.or, [41, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16558535637132752415 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20307_aux

theorem PEqualNP.Outside.L_meta_20307 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (16558535637132752415 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20307_aux.main
