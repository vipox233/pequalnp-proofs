import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19952_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [11, 5]⟩, ⟨.or, [6, 7]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [0, 13]⟩, ⟨.or, [16, 6]⟩, ⟨.or, [11, 19]⟩, ⟨.or, [1, 9]⟩, ⟨.or, [10, 18]⟩, ⟨.and, [20, 22]⟩, ⟨.or, [15, 4]⟩, ⟨.or, [7, 18]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [21, 27]⟩, ⟨.or, [12, 24]⟩, ⟨.or, [5, 22]⟩, ⟨.and, [4, 15]⟩, ⟨.and, [23, 30]⟩, ⟨.and, [26, 28]⟩, ⟨.and, [17, 10]⟩, ⟨.or, [25, 14]⟩, ⟨.or, [21, 6]⟩, ⟨.or, [25, 30]⟩, ⟨.and, [35, 36]⟩, ⟨.or, [32, 29]⟩, ⟨.or, [39, 31]⟩, ⟨.or, [33, 38]⟩, ⟨.or, [19, 37]⟩, ⟨.or, [2, 40]⟩, ⟨.and, [42, 43]⟩, ⟨.or, [34, 41]⟩, ⟨.or, [45, 44]⟩], 46⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7837978282315423185 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19952_aux

theorem PEqualNP.Outside.L_meta_19952 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7837978282315423185 : ℕ).testBit (8 * u.val + v.val)) 31 :=
  PEqualNP.Outside.L_meta_19952_aux.main
