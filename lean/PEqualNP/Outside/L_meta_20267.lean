import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20267_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [8, 4]⟩, ⟨.or, [5, 0]⟩, ⟨.or, [14, 16]⟩, ⟨.or, [15, 0]⟩, ⟨.and, [10, 6]⟩, ⟨.or, [9, 2]⟩, ⟨.or, [13, 7]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [3, 10]⟩, ⟨.or, [11, 24]⟩, ⟨.or, [6, 22]⟩, ⟨.or, [25, 19]⟩, ⟨.or, [16, 19]⟩, ⟨.or, [24, 21]⟩, ⟨.or, [5, 20]⟩, ⟨.or, [28, 22]⟩, ⟨.or, [14, 29]⟩, ⟨.or, [27, 6]⟩, ⟨.or, [18, 30]⟩, ⟨.or, [32, 1]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [36, 23]⟩, ⟨.or, [31, 12]⟩, ⟨.and, [38, 35]⟩, ⟨.or, [26, 21]⟩, ⟨.and, [37, 40]⟩, ⟨.and, [33, 34]⟩, ⟨.or, [39, 41]⟩, ⟨.or, [42, 43]⟩], 44⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6799783216241292135 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20267_aux

theorem PEqualNP.Outside.L_meta_20267 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (6799783216241292135 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_20267_aux.main
