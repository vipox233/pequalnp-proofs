import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20108_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [3, 1]⟩, ⟨.or, [9, 7]⟩, ⟨.or, [14, 6]⟩, ⟨.or, [18, 8]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [10, 19]⟩, ⟨.or, [8, 13]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [13, 20]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [7, 23]⟩, ⟨.and, [26, 10]⟩, ⟨.or, [26, 25]⟩, ⟨.or, [24, 18]⟩, ⟨.and, [28, 0]⟩, ⟨.or, [5, 12]⟩, ⟨.or, [23, 31]⟩, ⟨.and, [28, 9]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [29, 32]⟩, ⟨.or, [31, 21]⟩, ⟨.or, [2, 11]⟩, ⟨.and, [36, 37]⟩, ⟨.and, [3, 34]⟩, ⟨.and, [16, 22]⟩, ⟨.or, [35, 27]⟩, ⟨.or, [41, 40]⟩, ⟨.or, [42, 33]⟩, ⟨.or, [43, 38]⟩, ⟨.or, [44, 30]⟩, ⟨.or, [39, 45]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10852103239182430665 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20108_aux

theorem PEqualNP.Outside.L_meta_20108 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (10852103239182430665 : ℕ).testBit (8 * u.val + v.val)) 32 :=
  PEqualNP.Outside.L_meta_20108_aux.main
