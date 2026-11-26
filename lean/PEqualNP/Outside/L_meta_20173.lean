import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20173_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [1, 12]⟩, ⟨.or, [11, 5]⟩, ⟨.or, [13, 3]⟩, ⟨.or, [4, 8]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [2, 14]⟩, ⟨.or, [7, 20]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [21, 16]⟩, ⟨.or, [24, 15]⟩, ⟨.or, [21, 19]⟩, ⟨.or, [15, 19]⟩, ⟨.or, [6, 26]⟩, ⟨.or, [22, 28]⟩, ⟨.and, [28, 18]⟩, ⟨.or, [14, 17]⟩, ⟨.and, [23, 29]⟩, ⟨.or, [22, 18]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [32, 30]⟩, ⟨.and, [33, 25]⟩, ⟨.or, [6, 31]⟩, ⟨.or, [10, 12]⟩, ⟨.and, [37, 27]⟩, ⟨.and, [34, 38]⟩, ⟨.or, [35, 40]⟩, ⟨.or, [36, 39]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15178139455177243725 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_20173_aux

theorem PEqualNP.Outside.L_meta_20173 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (15178139455177243725 : ℕ).testBit (8 * u.val + v.val)) 28 :=
  PEqualNP.Outside.L_meta_20173_aux.main
