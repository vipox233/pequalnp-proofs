import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19908_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 4]⟩, ⟨.or, [2, 9]⟩, ⟨.or, [16, 3]⟩, ⟨.or, [6, 15]⟩, ⟨.or, [13, 10]⟩, ⟨.or, [5, 11]⟩, ⟨.or, [16, 7]⟩, ⟨.or, [13, 22]⟩, ⟨.or, [7, 23]⟩, ⟨.or, [5, 14]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [2, 21]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [25, 25]⟩, ⟨.or, [19, 18]⟩, ⟨.or, [17, 1]⟩, ⟨.or, [0, 24]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [27, 28]⟩, ⟨.and, [32, 34]⟩, ⟨.or, [21, 1]⟩, ⟨.or, [36, 9]⟩, ⟨.or, [33, 29]⟩, ⟨.or, [37, 33]⟩, ⟨.or, [10, 38]⟩, ⟨.and, [39, 30]⟩, ⟨.and, [31, 40]⟩, ⟨.or, [26, 5]⟩, ⟨.or, [42, 35]⟩, ⟨.and, [20, 43]⟩, ⟨.or, [41, 45]⟩, ⟨.or, [44, 46]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17022383772369540555 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19908_aux

theorem PEqualNP.Outside.L_meta_19908 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (17022383772369540555 : ℕ).testBit (8 * u.val + v.val)) 35 :=
  PEqualNP.Outside.L_meta_19908_aux.main
