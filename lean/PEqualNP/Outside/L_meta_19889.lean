import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19889_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [9, 6]⟩, ⟨.or, [7, 10]⟩, ⟨.or, [4, 7]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [15, 14]⟩, ⟨.or, [19, 3]⟩, ⟨.or, [17, 0]⟩, ⟨.or, [22, 19]⟩, ⟨.and, [21, 22]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [2, 11]⟩, ⟨.or, [16, 3]⟩, ⟨.and, [27, 14]⟩, ⟨.or, [13, 25]⟩, ⟨.or, [14, 0]⟩, ⟨.or, [27, 30]⟩, ⟨.or, [12, 24]⟩, ⟨.or, [31, 26]⟩, ⟨.or, [32, 4]⟩, ⟨.or, [34, 26]⟩, ⟨.or, [34, 20]⟩, ⟨.or, [16, 23]⟩, ⟨.or, [36, 23]⟩, ⟨.or, [9, 13]⟩, ⟨.and, [5, 38]⟩, ⟨.or, [28, 29]⟩, ⟨.and, [33, 41]⟩, ⟨.and, [21, 39]⟩, ⟨.or, [42, 40]⟩, ⟨.and, [35, 37]⟩, ⟨.or, [45, 44]⟩, ⟨.or, [43, 46]⟩], 47⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6627281390824537785 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19889_aux

theorem PEqualNP.Outside.L_meta_19889 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6627281390824537785 : ℕ).testBit (8 * u.val + v.val)) 34 :=
  PEqualNP.Outside.L_meta_19889_aux.main
