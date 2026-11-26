import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19948_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [6, 14]⟩, ⟨.or, [10, 8]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [15, 0]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [6, 19]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [21, 7]⟩, ⟨.or, [18, 8]⟩, ⟨.or, [21, 20]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [27, 16]⟩, ⟨.or, [23, 17]⟩, ⟨.or, [0, 26]⟩, ⟨.or, [18, 22]⟩, ⟨.or, [14, 15]⟩, ⟨.or, [29, 24]⟩, ⟨.and, [28, 34]⟩, ⟨.and, [32, 30]⟩, ⟨.and, [29, 22]⟩, ⟨.or, [33, 31]⟩, ⟨.or, [10, 37]⟩, ⟨.and, [25, 26]⟩, ⟨.or, [35, 36]⟩, ⟨.or, [4, 40]⟩, ⟨.or, [39, 42]⟩, ⟨.and, [43, 38]⟩, ⟨.or, [44, 41]⟩], 45⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7582498071666593340 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19948_aux

theorem PEqualNP.Outside.L_meta_19948 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7582498071666593340 : ℕ).testBit (8 * u.val + v.val)) 30 :=
  PEqualNP.Outside.L_meta_19948_aux.main
