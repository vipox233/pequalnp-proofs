import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19863_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def C_ : Circuit := ⟨[⟨.or, [15, 7]⟩, ⟨.or, [9, 6]⟩, ⟨.or, [1, 17]⟩, ⟨.or, [1, 16]⟩, ⟨.or, [14, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [13, 8]⟩, ⟨.or, [10, 0]⟩, ⟨.or, [23, 16]⟩, ⟨.or, [9, 24]⟩, ⟨.or, [22, 3]⟩, ⟨.and, [26, 25]⟩, ⟨.or, [5, 23]⟩, ⟨.or, [13, 18]⟩, ⟨.and, [21, 11]⟩, ⟨.and, [20, 29]⟩, ⟨.or, [8, 19]⟩, ⟨.and, [0, 19]⟩, ⟨.or, [33, 20]⟩, ⟨.or, [27, 31]⟩, ⟨.or, [18, 11]⟩, ⟨.or, [30, 35]⟩, ⟨.or, [12, 4]⟩, ⟨.or, [34, 36]⟩, ⟨.and, [39, 38]⟩, ⟨.and, [32, 28]⟩, ⟨.or, [40, 37]⟩, ⟨.or, [41, 42]⟩], 43⟩

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

theorem main : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2691051730525901985 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  ⟨C_, monoTwoB_sound C_ (by decide +kernel), by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_19863_aux

theorem PEqualNP.Outside.L_meta_19863 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (2691051730525901985 : ℕ).testBit (8 * u.val + v.val)) 29 :=
  PEqualNP.Outside.L_meta_19863_aux.main
